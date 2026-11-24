# SRC-1288–1306　膜の荷電端、余剰次元の選択、磁気的な地平線

2026-11-22。第4論文R.7–R.15の出典・先行結果の対象範囲。出版記録・arXiv著者版・公開本文を用いた。書誌・[主張と検証](../../results/RES-0109.md)。前回確認したPage電荷、D2の背景二形式、太陽系のCassini測定については[前節の原著調査](wrapped-membrane-capture.md)を引き継いだ。

| ID | 原著と根拠 | 今回の計算で使った範囲 |
|---|---|---|
| SRC-1288 | E. Witten, *On Flux Quantization in M-Theory and the Effective Action*, [hep-th/9609122v1](https://arxiv.org/abs/hep-th/9609122v1) | 三形式の量子化と12次元の位相。重力による量子化のシフトがある。トーラスで混合係数を比較する本稿の単純化を一般の多様体へ外挿しない |
| SRC-1289 | F. Brümmer, J. Jaeckel, V. V. Khoze, *Magnetic Mixing*, [0905.0633](https://arxiv.org/abs/0905.0633) | 混合位相項が磁気単極子に別部門の有効電荷を与える先例。異なる観測者の宇宙を同一視する理論ではない |
| SRC-1290 | Y. Imamura, *Born-Infeld Action and Chern-Simons Term from Kaluza-Klein Monopole in M-theory*, [hep-th/9706144](https://arxiv.org/abs/hep-th/9706144) | 十一次元のKK単極子からD6の世界体のベクトルと作用の二次項等を再現。全次数のDBIをこの計算で証明したとは解釈しない |
| SRC-1291 | A. Sen, *Kaluza-Klein Dyons in String Theory*, [hep-th/9705212](https://arxiv.org/abs/hep-th/9705212) | KK単極子におけるコンパクトな集合座標とダイオン。今回の二種類のT双対枠や混合余鎖の同定は別途計算 |
| SRC-1292 | A. Chatrabhuti, *Target Space Duality and Moduli Stabilization in String Gas Cosmology*, [hep-th/0602031、式(26)](https://arxiv.org/pdf/hep-th/0602031) | 特に近い先行研究。半単位のB場と正三角形の格子をもつSU(3)増大点を明記し、弦ガスによる安定性を考察。幾何も双対固定点も本稿の新規性には含めない |
| SRC-1293 | A. Kaya, *Brane Gases and Stabilization of Shape Moduli with Momentum and Winding Stress*, [hep-th/0504208](https://arxiv.org/abs/hep-th/0504208) | 巻数・運動量を含む物質応力による形状の力学。二形式を含む二成分のBPS静止質量を今回の三種の占有で評価した |
| SRC-1294 | H. L. Montgomery, *Minimal Theta Functions*, [Glasgow Math. J. 30, 75–85](https://doi.org/10.1017/S0017089500007047) | 面積固定の二次元格子でのガウス和の最小定理。正の積分核を介して正味中性の一対の内部自由エネルギーへ適用。非原始電荷の縮退や並進気体の一般的な分配関数は含まない |
| SRC-1295 | F. Epple, D. Lüst, *Tachyon Condensation for Intersecting Branes at Small and Large Angles*, [hep-th/0311182](https://arxiv.org/abs/hep-th/0311182) | 二枚の角度つきブレーンと開弦の質量。しきい値は今回の電荷で \(\vartheta=\pi/3\) として評価 |
| SRC-1296 | M. G. Jackson, N. T. Jones, J. Polchinski, *Collisions of Cosmic F- and D-strings*, [hep-th/0405229](https://arxiv.org/abs/hep-th/0405229) | 交差時の弦生成・再結合確率が状況に依存すること。開弦の特定モードの対生成を終了した再結合と数えない |
| SRC-1297 | T. T. Wu, C. N. Yang, *Dirac monopole without strings: monopole harmonics*, [Nucl. Phys. B 107, 365](https://doi.org/10.1016/0550-3213(76)90143-7) | 単極子調和関数の角運動量、最小 \(j=|nm|/2\)。スカラーの角運動量を通常の整数部分波と置き換えない |
| SRC-1298 | L. Fehér, P. A. Horváthy, *Dynamical symmetry of the Kaluza-Klein monopole*, [0902.4600v2](https://arxiv.org/abs/0902.4600v2) | KK単極子のスカラー運動とクーロン問題。正・負のNUTパラメータや滑らかな境界条件の違いに注意する |
| SRC-1299 | C. F. E. Holzhey, F. Wilczek, *Black Holes as Elementary Particles*, [hep-th/9202014](https://arxiv.org/abs/hep-th/9202014) | 結合指数が1を超えるディラトン黒穴の近極限で形式的Hawking温度が上がる一方、外部との熱接触は障壁で妨げられる。高温と小さな透過率の両立は既知 |
| SRC-1300 | D. Rasheed, *The Rotating Dyonic Black Holes of Kaluza-Klein Theory*, [hep-th/9505038](https://arxiv.org/abs/hep-th/9505038) | 5次元真空重力からの4次元KK黒穴。本稿で使うのは純磁気・無回転解 |
| SRC-1301 | F. Larsen, *Rotating Kaluza-Klein Black Holes*, [hep-th/9909102v3](https://arxiv.org/abs/hep-th/9909102v3) | 磁荷・電荷・角運動量・極限質量。吸収後の物体を一つの定常黒穴として扱える必要条件 |
| SRC-1302 | R. Emparan, G. T. Horowitz, *Microstates of a Neutral Black Hole in M Theory*, [hep-th/0607023](https://arxiv.org/abs/hep-th/0607023) | KK/D0–D6系の量子化された電磁荷と質量の規格化。今回の物質が実際に吸収される確率や蒸発の終状態までを与える主張はない |
| SRC-1303 | J. D. Bekenstein, A. Meisels, *Einstein A and B coefficients for a black hole*, [Phys. Rev. D 15, 2775](https://journals.aps.org/prd/abstract/10.1103/PhysRevD.15.2775) | ブラックホールでの一モード入出力・誘導放出の統計の先例。受信時の条件付き偶奇計数を本稿の磁気部分波に適用 |
| SRC-1304 | A. Sen, *String Network*, [hep-th/9711130](https://arxiv.org/abs/hep-th/9711130) | 三種類の電荷が会合するBPSネットワーク。今回の希薄な独立粒子三種や、その熱平衡安定性を同じ物理系とはみなさない |
| SRC-1305 | D. Gottesman, *Stabilizer Codes and Quantum Error Correction*, [quant-ph/9705052](https://arxiv.org/abs/quant-ph/9705052) | 二元シンプレクティック形式と独立な検査の数による識別は既知。今回は物質が受けた巻き付き電荷の集合から各観測者が分ける層を定める仮説を比較 |

### 新規性を調べた範囲

英語の論題・要旨・本文を、mixed Witten effect / C field flux quantization / D4 induced charge / Taub NUT zero mode、hexagonal lattice / string gas / BPS brane gas / momentum winding / frozen moduli、brane recombination / angled open strings、charged scalar / magnetic Kaluza Klein greybody / D0 D6 near extremal absorption、single incoming quantum / black hole stimulated emission / parity、wrapped cycles / material records / binary symplectic checks の組合せで調べた。特殊関数の規約はNISTの[Coulombの原点での規格化](https://dlmf.nist.gov/33.2)と[Legendre関数の大引数展開](https://dlmf.nist.gov/14.8)でも照合できる。

個々の混合位相、六角格子、BPS質量、角度付きの開弦、黒穴の透過と誘導放出、偶奇検査はいずれも既知である。本稿で新たに導出したのは、受信した荷電端の直接作用と二つの指定基底の半位相に対し、物質の占有を保存・緩和した場合の選択が同一の格子で逆転する条件、最低二部分波の透過比と単位入射の偶奇条件付け、到着した巻数が観測者ごとに定める最小の識別の組合せである。今回の調査でこの組合せを同じ設定で導いた原著は特定できなかった。全先行研究に対する優先権や根本作用の一意性までは確認できない。

連続量の受信の先行研究として M. Ozawa, *Quantum measuring processes of continuous observables*, [J. Math. Phys. 25, 79](https://doi.org/10.1063/1.526000)を参照した。ガウス雑音つき受信の条件付き平均と密度の微分に関する一般論は B. Efron, *Tweedie's Formula and Selection Bias*, [JASA (2011)](https://doi.org/10.1198/jasa.2011.tm11181)と整合する。既知の連続測定を用いて受信の精度とボルン測度を求めた。時空を共有しない観測者の根本的な選択、一般の重力場がいつこの装置の役割を果たすかをこれらの文献に帰属させない。

SRC-1306。P. C. Peters, J. Mathews, *Gravitational Radiation from Point Masses in a Keplerian Orbit*, [Phys. Rev. 131, 435](https://journals.aps.org/pr/abstract/10.1103/PhysRev.131.435)を四重極放射の基準に用いた。W. D. Goldberger, I. Z. Rothstein, *Dissipative Effects in the Worldline Approach to Black Hole Dynamics*, [式(20)–(24)](https://arxiv.org/pdf/hep-th/0511133)で四次元のWeylテンソルの受信作用と一偏極の吸収断面積 \(4\pi r_s^6\omega^4/45\) を照合した。これらの標準的な較正から今回の源と受け手の整合率、角運動量を残した場合と熱だけを残した場合の事後分布を別途導いた。
