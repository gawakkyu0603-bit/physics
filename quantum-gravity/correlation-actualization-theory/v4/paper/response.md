# Response to the technical review of Version 3

Yohtaro Soga · Version 4 · 25 November 2026

The reviewer supported publication of the conditional sector construction within the scope examined. The three earlier substantive issues and the earlier recommendations were considered resolved. The report identified two optional editorial improvements. Its assessment concerns technical review; a journal decision is separate.

| Item | Author response |
|---|---|
| E1. Identify the operation used to randomize the final measurement. | Adopted. The supplement now gives the computational-basis Pauli \(X=|0\rangle\langle1|+|1\rangle\langle0|\), defines the return eigenstates, and explains why each reference keeps its identity. The randomization changes the sign of the off-diagonal readout term. [Readout calibration](supp-calibration.tex) |
| E2. Point readers from the inclusive condition to the outcome-resolved condition. | Adopted. Article §2.1 now states that an exchange of incomparable contacts must also preserve the maps for each pair of retained outcomes and their subsequent control. It points to the history law in §3 and the worked example in supplement §4.1. [Effective interaction](main.tex) · [Outcome order](supp-domains.tex) |

The author also asked how the proposal for a theory of everything relates to the finite systems tested. The revised abstract, article §3.2 and conclusion make the distinction explicit. CAT proposes one form of the action across admissible matrix sizes. At chosen rank, clock and physical port the history operation uses complete scattering blocks. An all-rank or continuum theory requires compatible preparations, observables and probabilities; no such limit or physical sector measure has been obtained. The new reading guide locates the infall motivation, comparison of effective interactions, matrix parent, observational tests and shared spacetime on actual PDF pages. [Guide to the six questions](reading-guide.md)

Version 3 was reviewed against ZIP SHA-256 `d55f07d964126d5417e8aa5fd2d2121a561f726677b640f9b43258fe5f585731`. The reviewer reports running the nine numerical drivers (59 groups, 1,195 floating-point values) and ten Lean modules (365 declarations) under Linux. The formal claims keep their stated mathematical assumptions. Version 4 is an editorial revision. Its numerical inputs, reference results, drivers, Lean sources and underlying 91 records were checked against their Version 3 hashes. [Verification details](evidence/verification.json) · [Response in Version 3](response-v3.md)

