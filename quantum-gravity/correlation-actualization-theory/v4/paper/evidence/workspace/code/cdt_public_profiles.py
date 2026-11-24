"""Fetch CRC-checked profile headers from a fixed Zenodo release or reanalyse local headers."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import re
import struct
import time
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen
import zlib

import numpy as np
from scipy.optimize import brentq

ROOT = Path(__file__).resolve().parents[1]
PROFILE = ROOT/"data"/"cdt-20589545-profiles.json"
RESULT = ROOT/"verification"/"public-cdt-results.json"
RECORD = "https://zenodo.org/records/20589545"
ARCHIVES = {"60-80k.zip":303572127, "80-160k.zip":768607044, "80-320k.zip":316470820}


def read_range(archive, first, last):
    url = f"{RECORD}/files/{archive}?download=1&profile_range={first}-{last}"
    for attempt in range(6):
        request = Request(url, headers={"Range":f"bytes={first}-{last}", "Accept-Encoding":"identity",
                                        "User-Agent":"Soga-CDT-profile-analysis/1.0"})
        try:
            with urlopen(request, timeout=30) as reply:
                expected = f"bytes {first}-{last}/{ARCHIVES[archive]}"
                if reply.status!=206 or reply.headers.get("Content-Range")!=expected:
                    raise ValueError(f"Unexpected HTTP range for {archive}, {first}, {last}")
                body = reply.read(last-first+2)
                if len(body)!=last-first+1:
                    raise ValueError("Incomplete range")
                return body
        except (HTTPError, URLError, TimeoutError, ConnectionError) as error:
            if isinstance(error,HTTPError) and error.code not in (408,429,500,502,503,504):
                raise
            if attempt==5:
                raise
            retry = error.headers.get("Retry-After", "") if isinstance(error, HTTPError) else ""
            time.sleep(max(2**attempt, int(retry) if retry.isdigit() else 0))


def catalog(archive):
    size = ARCHIVES[archive]
    tail = read_range(archive, size-65557, size-1)
    footer = tail.rfind(b"PK\x05\x06")
    assert footer>=0
    _,disk,cdisk,on_disk,total,length,offset,_ = struct.unpack_from("<4s4H2IH",tail,footer)
    assert disk==cdisk==0 and total==on_disk
    directory = read_range(archive,offset,offset+length-1)
    index = {}
    position = 0
    for _ in range(total):
        fields = struct.unpack_from("<4s6H3I5H2I",directory,position)
        assert fields[0]==b"PK\x01\x02"
        name_len, extra_len, comment_len = fields[10:13]
        name = directory[position+46:position+46+name_len].decode("utf8")
        position += 46+name_len+extra_len+comment_len
        match = re.search(r"(conf-[^/]+?\.cdt)(?:_|$)", name)
        if match and name.endswith(".txt") and fields[4]==8:
            conf = match.group(1)
            entry = dict(configuration=conf, name=name, offset=fields[-1],
                         size=fields[8], uncompressed=fields[9], crc=fields[7])
            if conf not in index or name<index[conf]["name"]:
                index[conf] = entry
    assert position==length and index
    ordered = sorted(index, key=lambda c: hashlib.sha256(c.encode()).digest())
    return total,len(index),[index[c] for c in ordered[:64]]


def read_profile(archive, entry):
    offset = entry["offset"]
    # Cover the short local header and complete compressed stream in one request in the usual case.
    header = read_range(archive,offset,min(ARCHIVES[archive]-1,offset+entry["size"]+511))
    values = struct.unpack_from("<4s5H3I2H",header)
    name_size,extra_size = values[-2:]
    assert values[0]==b"PK\x03\x04" and values[3]==8
    start = 30+name_size+extra_size
    if start>=len(header):
        header = read_range(archive,offset,offset+start-1)
    assert header[30:30+name_size].decode("utf8")==entry["name"]
    payload = header[start:]
    if len(payload)<entry["size"]:
        payload += read_range(archive,offset+max(start,len(header)),offset+start+entry["size"]-1)
    raw = zlib.decompress(payload[:entry["size"]],-15)
    assert len(raw)==entry["uncompressed"] and zlib.crc32(raw)==entry["crc"]
    first = raw.splitlines()[:4]
    assert entry["configuration"].encode() in first[0] and b"Timeslices with number" in first[1]
    return dict(configuration=entry["configuration"],member=entry["name"], crc32=f"{entry['crc']:08x}",
                sha256=hashlib.sha256(raw).hexdigest(), header=[s.decode("utf8") for s in first])


def fetch():
    cache = ROOT/".research-tools"/"cdt-profile-headers"
    cache.mkdir(parents=True,exist_ok=True)
    out = {}
    for archive in ARCHIVES:
        total,unique,sample = catalog(archive)
        def get(entry):
            name = hashlib.sha256((archive+entry["name"]).encode()).hexdigest()+".json"
            path = cache/name
            if path.exists():
                result = json.loads(path.read_text(encoding="utf8"))
                assert result["member"]==entry["name"] and result["crc32"]==f"{entry['crc']:08x}"
                return result
            record = read_profile(archive,entry)
            path.write_text(json.dumps(record)+"\n",encoding="utf8")
            return record
        print(archive, "unique configurations", unique, "drawing", len(sample), flush=True)
        with ThreadPoolExecutor(max_workers=3) as workers:
            records = list(workers.map(get, sample))
        out[archive] = dict(zip_entries=total, unique_configurations=unique, records=records)
    PROFILE.write_text(json.dumps(dict(source=RECORD,archives=out),indent=2)+"\n",encoding="utf8")


def shape(header):
    T = int(re.search(r"max timeslice:\s*(\d+)",header[0])[1])
    times,counts = (np.fromstring(line,sep=" ",dtype=int) for line in header[2:])
    assert np.array_equal(np.sort(times),np.arange(1,T+1)) and np.all(counts>0) and len(counts)==T
    total = int(sum(counts))
    roots = np.exp(2j*np.pi*times/T)
    first = np.dot(counts,roots)/total
    second = np.dot(counts,roots**2)/total
    if abs(first)<1e-12:
        return None
    anchor = (first.conjugate()/abs(first))**2
    marker = (roots**2*anchor).real
    return total,float((second*anchor).real),float(abs(first)),np.dot(counts,abs(marker))/total


def analyze():
    archives = json.loads(PROFILE.read_text(encoding="utf8"))["archives"]
    report = {}
    for name,archive in archives.items():
        ordered = sorted(archive["records"],key=lambda item:item["configuration"])
        rows = [shape(item["header"]) for item in ordered]
        good = [row for row in rows if row is not None]
        totals,values,amps,absolute = np.array(good).T
        m = len(values)
        def tilted(h):
            weights = np.exp(-h*values)
            return np.average(values,weights=weights), weights.sum()**2/np.dot(weights,weights)
        def stats(x):
            return np.array([np.mean(x), np.var(x,ddof=1)])
        jk = np.array([stats(np.delete(values, group)) for group in np.array_split(np.arange(m),8)])
        errors = np.sqrt(7/8*np.sum((jk-jk.mean(axis=0))**2,axis=0))
        plus,ep = tilted(1.)
        minus,em = tilted(-1.)
        grad = (tilted(1e-4)[0]-tilted(-1e-4)[0])/2e-4
        assert np.max(abs(values))<=1 and abs(grad+np.var(values))<1e-11
        assert plus<values.mean()<minus
        nominal = 1000*int(re.search(r"-(\d+)k",name)[1])
        centers,radii = values*totals/nominal,absolute*totals/nominal
        critical = np.max((centers[:,None]-centers[None,:])/(radii[:,None]+radii[None,:]))
        def variance_floor(eta):
            low,high = centers-eta*radii, centers+eta*radii
            def gradient(z):
                return np.sum(z-np.clip(z,low,high))
            z = brentq(gradient,low.min()-1,high.max()+1)
            selected = np.clip(z,low,high)
            bound = np.mean((selected-z)**2)
            assert abs(bound-np.var(selected))<1e-13
            assert (bound>1e-14)==(eta<critical)
            return bound
        ratio_sq = ((1-critical)/(1+critical))**2
        report[name] = dict(archive_unique=archive["unique_configurations"], retrieved=len(rows), excluded=len(rows)-m,
                            mean_total_four_simplices=totals.mean(), minimum_first_amplitude=amps.min(),
                            mean_shape=values.mean(), mean_jackknife=errors[0], empirical_variance=np.var(values),
                            unbiased_variance=np.var(values,ddof=1), variance_jackknife=errors[1],
                            tilted_plus=plus,tilted_minus=minus,ess_plus=ep,ess_minus=em,
                            slope_from_perturbation=grad,nominal_N41=nominal,shape_tolerance=critical,
                            assumed_relative_type_volume_difference=.02,relaxed_physical_variance_lower=variance_floor(.02),
                            minimum_euclidean_alpha_for_certificate=(7-3*ratio_sq)/(12-8*ratio_sq),
                            uniform_variance_floor_alpha_at_least_one=variance_floor(5-2*np.sqrt(6)))
    RESULT.write_text(json.dumps(report,indent=2)+"\n",encoding="utf8")
    print(json.dumps(report,indent=2))


if __name__=="__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch", action="store_true", help="Rebuild the checked headers from Zenodo before analysis")
    if parser.parse_args().fetch:
        fetch()
    analyze()
