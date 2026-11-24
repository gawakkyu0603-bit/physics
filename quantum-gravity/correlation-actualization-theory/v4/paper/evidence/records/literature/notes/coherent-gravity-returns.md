# SRC-1258–1267　膜の再散乱、重力場の復帰、物質が保存できる電荷

2026-11-22。第4論文付録Q・[比較結果](../../results/RES-0107.md)。既知の手法、本研究で追加した物理条件、優先性が未確定の範囲を記す。

| ID | 照合した文献 | この比較での役割 |
|---|---|---|
| SRC-1258 | P. Busch, J. Singh, *Lüders theorem for unsharp quantum measurements*. [著者原稿](https://arxiv.org/abs/1304.0054)・[掲載版](https://doi.org/10.1016/S0375-9601(98)00704-X) | 鋭い射影で観測したときに別の量の統計が保たれる可換条件。一般の非鋭い観測全体には単純に拡張できない。 |
| SRC-1259 | T. Heinosaari, M. M. Wolf, *Non-disturbing quantum measurements*. [v2](https://arxiv.org/abs/1005.5659v2) | 非擾乱、同時測定可能性、可換性の関係。本文Q.1はすべての準備で鋭い受信電荷の書込みを保護する場合に限る。 |
| SRC-1260 | M. Gell-Mann, J. B. Hartle, *Strong decoherence*. [原著](https://arxiv.org/abs/gr-qc/9509054) | 過去の記録の持続性を強いデコヒーレンスで扱う。既知の考え方。ここでは受信物質が持つ電荷の代数と、同じ重力作用が許す再散乱を個別に与えた。 |
| SRC-1261 | S. Wimberger, I. Guarneri, S. Fishman, *Quantum resonances and decoherence for delta-kicked atoms*. [原著](https://arxiv.org/abs/nlin/0212033)・[DOI](https://doi.org/10.1088/0951-7715/16/4/312) | 原子の反復キック、半Talbot時間、自然放出によるコヒーレンスの変化。運動量の整数性による復帰は既知。膜の全高調波、剰余ごとの永久化と同じ場の復帰を比較したのが今回の応用。 |
| SRC-1262 | D. Dürr, S. Goldstein, R. Tumulka, N. Zanghì, *Quantum Hamiltonians and stochastic jumps*. [v3](https://arxiv.org/abs/quant-ph/0303056v3) | ハミルトニアンと波動関数からボルン分布を保つ最小跳躍率を構成する。すべての隠れた跳躍を局所で読める物理記録とする主張はこの原著のものではない。 |
| SRC-1263 | L. P. Hughston, R. Jozsa, W. K. Wootters, *A complete classification of quantum ensembles having a given density matrix*. [掲載版](https://doi.org/10.1016/0375-9601(93)90880-9) | 同じ密度行列の異なる分解と、純粋化の別部分の測定による各分解の実現。初期の最小跳躍流量の反例に用いた。 |
| SRC-1264 | G. M. Palma, K.-A. Suominen, A. K. Ekert, *Quantum computers and dissipation*. [原著](https://arxiv.org/abs/quant-ph/9702001) | 量子レジスタと共通環境、真空または熱浴での位相緩和。Ohmic浴の消失を新しい基本法則とは数えない。 |
| SRC-1265 | T. Oniga, C. H.-T. Wang, *Quantum coherence, radiance, and resistance of gravitational systems*. [原著](https://arxiv.org/abs/1701.04122)・[PRD](https://doi.org/10.1103/PhysRevD.96.084014) | 四次元の束縛源の量子四重極放射。一般次元の局所源の指数は位相空間と曲率の微分数から求めた。コンパクト運動量別の複合粒子の形状因子はこの原著で計算されていない。 |
| SRC-1266 | NIST DLMF, ch. 10, *Bessel functions*. [Jの積分表示](https://dlmf.nist.gov/10.9#E1)・[Kの積分表示](https://dlmf.nist.gov/10.32#E9)・[Jの規格化と級数](https://dlmf.nist.gov/10.2#E2) | 円での位相平均、正の積分からの高調波上界、交代級数の規約を照合した。 |
| SRC-1267 | W. B. Jones, O. Njåstad, W. J. Thron, *Moment theory, orthogonal polynomials, quadrature, and continued fractions associated with the unit circle*. [掲載版](https://doi.org/10.1112/blms/21.2.113) | 円周上の正の求積公式と直交性。等重みの正多角形が作る有限モーメントの消失は既知の数学。今回の適用は、KK重力を受信した物質が符号を選べる最少の位相応答数と、自然な捕獲で残る符号の分布にある。 |

11次元の計量に由来する十次元IIAの1形式とD0電荷は[Witten](https://arxiv.org/abs/hep-th/9503124)を参照。読出し能力は量子状態の[最適識別](https://arxiv.org/abs/quant-ph/9604001)・[誤りのない識別](https://arxiv.org/abs/quant-ph/9807022)に基づく。電荷を持つ物質がかかわるのは各層内の向きの基準である。

膜の一次資料は J. Polchinski, P. Pouliot の[単位M運動量移送](https://arxiv.org/abs/hep-th/9704029)と、S. Paban, S. Sethi, M. Stern の[四微分作用](https://arxiv.org/abs/hep-th/9808119)。原著が保護するのはこの相互作用の係数であり、二度の直線軌道、励起の吸収時刻、観測者ごとの確定やBFSSの全散乱行列ではない。重力が異なる経路を結ぶ考え方の先例としてP. C. E. Stampの[相関世界線模型](https://arxiv.org/abs/1506.05065)も照合した。可逆な経路の引き寄せだけでは反跳物質に不可逆な記録を選ぶ則は決まらない。線形な独立場を積分すると同じ因果的な非局所作用が得られることは[Feynman–Vernon](https://doi.org/10.1016/0003-4916(63)90068-X)に基づく。

検索には membrane M-momentum transfer, compact charge parity, membrane eikonal recoil, intermediate momentum record, kicked-rotor antiresonance, nondisturbing quantum measurements, correlated worldlines, Bell jump events, independent boson / gravitational tidal dephasing の組合せを用いた。対象とした著者原稿で、D2/M2の全移送に対する符号の限界、重力で捕獲された電荷と生残成分での復帰の分散制約、および同じ場の復帰と中間での剰余の永久化を合わせた式は確認できなかった。共通の数学の既知性、検索の不完全性、未公開研究の可能性から、国際的な先取権は確定していない。
