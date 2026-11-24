"""Rebuild the local supernova sample from the official, pinned Pantheon+ release."""
import hashlib
import io
import json
from pathlib import Path
from urllib.parse import quote
from urllib.request import urlopen

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
REVISION = "c447f0fea703fcd0fff57de5000947b5ca81286b"
BASE = f"https://raw.githubusercontent.com/PantheonPlusSH0ES/DataRelease/{REVISION}/"
FILES = ("Pantheon+SH0ES.dat", "Pantheon+SH0ES_STAT+SYS.cov")


def prepare():
    content = []
    manifest = dict(revision=REVISION, source={})
    for name in FILES:
        url = BASE + quote("Pantheon+_Data/4_DISTANCES_AND_COVAR/"+name, safe="/")
        with urlopen(url, timeout=75) as response:
            raw = response.read()
        content.append(raw)
        manifest["source"][name] = dict(url=url, sha256=hashlib.sha256(raw).hexdigest(),
                                        bytes=len(raw))
    rows = np.genfromtxt(io.BytesIO(content[0]), names=True, dtype=None, encoding="ascii")
    raw_cov = np.fromstring(content[1].decode("ascii"), sep=" ")
    n = int(raw_cov[0])
    assert n == len(rows) and len(raw_cov) == 1+n*n
    choose = ((rows["zHD"]>.023) & (rows["zHD"]<.09) & (rows["IS_CALIBRATOR"]==0)
              & (rows["DEC"]>=-90) & (rows["DEC"]<=90) & (rows["RA"]>=0) & (rows["RA"]<360))
    index = np.flatnonzero(choose)
    cov = raw_cov[1:].reshape(n,n)[np.ix_(index,index)]
    np.testing.assert_allclose(cov,cov.T,atol=1e-10)
    dest = ROOT / "data/cat-pantheonplus-local.npz"
    columns = ("CID","IDSURVEY","zHD","zCMB","zHEL","m_b_corr","RA","DEC")
    np.savez_compressed(dest, row=index, cov=cov, **{k:rows[k][index] for k in columns})
    manifest.update(input_rows=n, sample_rows=len(index), distinct_SN=len(set(rows["CID"][index])),
                    selection="0.023 < zHD < 0.09; non-calibrator; finite sky coordinates in their physical intervals",
                    columns=list(columns), row_index="zero-based excluding header",
                    derived_arrays_sha256={k:hashlib.sha256(v.tobytes()).hexdigest()
                                           for k,v in np.load(dest,allow_pickle=False).items()})
    (ROOT/"data/cat-pantheonplus-provenance.json").write_text(json.dumps(manifest,indent=2)+"\n",
                                                               encoding="utf8")
    print(f"{n} input rows, {len(index)} selected, {manifest['distinct_SN']} distinct supernovae")


if __name__ == "__main__":
    prepare()
