# Four-dimensional CDT profiles used in the response calculation

Axel Maas, Simon Plätzer and Felix Pressler produced the simulated triangulations and the per-configuration text files. Their dataset is *Stochastic samples for the CDT geon propagator from “Hints for a Geon from Causal Dynamic Triangulations”*, v1, June 8, 2026, Zenodo DOI 10.5281/zenodo.20589545. The original data are distributed under [Creative Commons Attribution 4.0](https://creativecommons.org/licenses/by/4.0/). The original simulation and measurement protocols are documented in [the article](https://doi.org/10.1016/j.physletb.2026.140600) and [the data release](https://zenodo.org/records/20589545).

The included JSON contains excerpts of the first four text lines of selected configuration files, their archive/member names, full-member SHA-256 and original CRC32. Line endings are represented by JSON strings. The selected fields identify the periodic slices and the number of four-simplices assigned to each slice. The curvature-pair samples following the header were omitted. Extraction, charge-source reweighting and interpretation are part of the present study. The original simulations contained no installed record apparatus.

| Archive | MD5 published by Zenodo for the complete archive |
|---|---|
| 60-80k.zip | f9da5869c0fe60f23d247a43dff91fd2 |
| 80-160k.zip | a8af5522b2eaeb3a9feeaaaf68fa3bed |
| 80-320k.zip | f0409da42df8b4beb51d22b4236657f2 |

The acquisition code downloads the ZIP member directory and selected complete compressed members by HTTP ranges. It checks the actual range, offset, member name, uncompressed length and CRC32. The complete-archive checksums above are metadata supplied by the depositor. The acquisition does not read all bytes in each archive. The checksum manifest of the reproduction package covers the derived JSON itself.

Run the analysis offline on the [archived headers](cdt-20589545-profiles.json) with the [analysis program](../code/cdt_public_profiles.py). Running it with the optional argument --fetch reconstructs the header collection from the DOI. The original choice of configurations uses the 64 smallest SHA-256 hashes of distinct configuration names, excluding repeat measurements of the same configuration.
