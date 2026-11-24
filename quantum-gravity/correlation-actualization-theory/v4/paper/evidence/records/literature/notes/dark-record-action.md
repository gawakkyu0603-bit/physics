# 同じ重力接触の応力と四次元の微視的作用

2026-11-22。文献照合 SRC-1515–1538、RES-0121。既刊の研究結果・本稿の追加仮定・今回検証した接続を分けた。検索では「wrapped brane gas dark matter」「M-theory Casimir hyperbolic flux volume」「lattice heat kernel」「circle Lévy generator quadratic two frequencies」「Bott index clock shift」「globally hyperbolic exotic R4」「tight binding uniform force」等を手がかりとした。照合は以下の原典の対象範囲に限る。

| ID | 原典 | 引用が支える内容 |
|---|---|---|
| 1515 | [Dubovsky, Hui, Nicolis & Son](https://arxiv.org/abs/1107.0731) | 保存する粒子数密度から流体の圧力を得る有効理論。落下記録のエネルギー密度を指定する研究ではない。 |
| 1516 | [Sandvik et al.](https://arxiv.org/abs/astro-ph/0212114) | 統一暗黒流体の圧力摂動が物質パワースペクトルを変える例。今回使う膜の状態方程式とは異なる。 |
| 1517 | [DESI DR2 II, v2, Table IV](https://arxiv.org/abs/2503.14738v2) | \(D_M/r_d,D_H/r_d,D_V/r_d\) と同一赤方偏移ビンの相関。前の資料に保存した表を再利用した。 |
| 1518 | [Riess et al.](https://arxiv.org/abs/2112.04510) | 幾何学的な距離・セファイド・Ia型超新星を結ぶ絶対較正の例。 |
| 1519 | [Freedman et al.](https://arxiv.org/abs/2408.06153) | JWST等による複数の独立な指標と系統誤差。二つの測定の優劣を仮定しない。 |
| 1520 | [Brown & Teitelboim](https://doi.org/10.1016/0550-3213(88)90559-7) | 膜の生成による真空フラックスの段階的変化。私的な量子相関の書込みとの同定は本研究の仮定。 |
| 1521 | [Bousso & Polchinski](https://arxiv.org/abs/hep-th/0004134) | 四形式の量子化と宇宙項への寄与。 |
| 1522 | [Sano & Suzuki](https://arxiv.org/abs/0907.2495) | 内部空間に巻いたブレーンの質量、電荷、暗黒物質候補。記録一回の放出量との関係は扱わない。 |
| 1523 | [Maldacena & Núñez](https://arxiv.org/abs/hep-th/0007018) | 特定の古典超重力の仮定下でのコンパクト化に対する制約。量子補正への一律の排除には使わない。 |
| 1524 | [De Luca, Silverstein & Torroba](https://arxiv.org/abs/2104.13380) | 七次元負曲率、内部七形式に双対な外部四形式、負のカシミールエネルギーによる三項の体積安定化。局在や歪みの解析を含む。三項ポテンシャル自体に独自性を主張しない。 |
| 1525 | [Menotti & Onofri](https://cds.cern.ch/record/134274) | 格子ゲージ理論の群上の熱核作用とVillain作用の関係。ここで扱うセルごとの三形式は別の適用。 |
| 1526 | [G. A. Hunt](https://doi.org/10.2307/1992917) | Lie群上の測度の畳込み半群と生成子。 |
| 1527 | [D. Applebaum](https://arxiv.org/abs/1006.4711) | 拡散と跳躍を含むコンパクト群上の無限分解可能な法則のフーリエ解析。 |
| 1528 | [D. Toniolo](https://doi.org/10.1007/s11005-022-01602-6) | 二つのユニタリ行列のBott指数と許容変形での不変性。 |
| 1529 | [Banks, Fischler, Shenker & Susskind](https://arxiv.org/abs/hep-th/9610043) | 11次元M理論の非摂動的提案。ここで使ったコンパクトなプラケットや不可逆な選択を同提案の帰結とは扱わない。 |
| 1530 | [R. Gompf](https://arxiv.org/abs/1705.06644) | 位相的な \(\mathbb R^4\) の異種微分構造と群作用。 |
| 1531 | [V. Chernov & S. Nemirovski](https://arxiv.org/abs/1201.6070) | 大域的双曲なLorentz計量を許す可縮な滑らかな四次元多様体の微分同相型は標準 \(\mathbb R^4\)。 |
| 1532 | [C. Brans](https://arxiv.org/abs/gr-qc/9404003) | 四次元の異種微分構造を局在させる構成。 |
| 1533 | [A. Bernal & M. Sánchez](https://arxiv.org/abs/gr-qc/0306108) | 大域的双曲時空の滑らかなCauchy面と分解。 |
| 1534 | [Korsch & Mossmann](https://arxiv.org/abs/quant-ph/0307203) | 一様な力を受ける一次元格子の伝播振幅。荷電した私的記録の仕事と中性帰還への適用は今回の計算。 |

**新規性の範囲。** 熱核・負曲率の安定化・膜による宇宙項の変更・巻いたブレーン・Bott指数・Bloch振動はいずれも既知である。二電荷での厳密な一致が拡散を強制すること自体は、Huntの跳躍測度の表現でも \(4(1-\cos\theta)-(1-\cos2\theta)=2(1-\cos\theta)^2\) から従う。本研究で導出・形式化したのは有限のずれを全電荷に伝える係数付き不等式、および黒穴の中性帰還と同じ分布から、安定半径に残る重みと電荷に必要な仕事を求めて親作用を選別する条件である。調べた原典にはこの物理的な組合せを見いださなかった。全分野での先取性は確定していない。

**SRC-1535.** エネルギーを運ぶ連続スペクトルの受け手への遷移には [Skrzypczyk, Short & Popescu](https://arxiv.org/abs/1302.2811) の仕事貯蔵系という先例がある。正の下限を持つ対向二モードに四形式の整数電荷を結合し、電荷区間の端、落下率、半径の安定帯、局所に残る位相を同じ移送で比較したのは本稿の候補である。

**SRC-1536–1538。** 外部M2の面積作用と三形式電荷は[Bergshoeff, Sezgin & Townsend](https://doi.org/10.1016/0370-2693(87)91272-X)と[Kallosh & Sorokin](https://arxiv.org/abs/hep-th/0501081)を参照した。薄壁の接合には上記SRC-1520を使用し、[Gregory, Moss & Withers](https://arxiv.org/abs/1401.0017)の種質量付きの異なる問題も確認した。既存の膜の核形成や体積安定化の再発見を主張しない。全書込み幅が正の体積安定帯に残るという条件を外部M2の張力と組み合わせ、観測値を入れずに泡半径の下限を得たのが今回の接続である。
