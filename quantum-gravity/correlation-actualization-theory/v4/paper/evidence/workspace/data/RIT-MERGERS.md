# DAT-0002　合体前後の放射の四元運動量

2026-11-21。RIT数値相対論グループの公開カタログから、非回転・ほぼ円軌道で質量比1、3/4、1/4の計5件を取得した。後二者は同じ初期条件のn100とn140。実天体のデータではない。[公開元](https://ccrgpages.rit.edu/~RITCatalog/)・[カタログ論文](https://arxiv.org/abs/1703.03423)・[全ファイルURLの相対位置とSHA-256](rit-merger-files.json)

生の形式はNR injection HDF5の振幅・位相ROM splineと、各シミュレーションのテキストメタデータ。HDF5の属性には LVC-internal と記されている。原データは公開元から取得する方式にし、配布ZIPには[積分後の数値](processed/rit-merger-flux.json)、取得手順、照合ハッシュ、コードを収録した。論文内では当該データが指定する研究文献も引用した。

プロジェクト、または再現ZIPにある workspace を起点に、Pythonと h5py、NumPy、SciPy のある環境で次を実行する。

~~~text
python code/rit_merger_flux.py --fetch
python code/record_lifetimes.py
~~~

一段目は公開原本10ファイルをハッシュ照合し data/raw/rit-mergers に保存する。既に存在する原本の内容は変えない。波形から計算した結果は data/processed/rit-merger-flux.json に保存される。二段目と再現ZIPの sample は、添付の積分結果だけでもオフラインで行える。

各 early と late は \((E,P_x,P_y,P_z)\) の順で、\(G=c=M_{\rm initial}=1\)。21モード \(\ell=2,3,4\) のニュースに球面上の \(1,\sin\theta\,e^{i\varphi},\cos\theta\) を挟み、最初の100Mを余弦で徐々に立ち上げ、ピーク光度後80Mまで積分した。元のファイルにない早期軌道や高次モードを補った運動量ではない。分割時刻5種、積分刻み、開始、差分導関数、\(\ell=4\) を外す検算を含む。表の Metadata は公開ページの丸めた一覧値に代えて、ハッシュを照合した各 run の final-kick 値を使用した。
