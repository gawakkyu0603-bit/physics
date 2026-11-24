"""Deterministic, bilingual explanatory SVGs. No original research data are changed."""
from html import escape
import textwrap

COLORS={'blue':'#245edb','teal':'#007e95','purple':'#7547bc','orange':'#bd620e','red':'#be493b','gray':'#58708f','ink':'#14223b'}
def label(ja,en,lang): return ja if lang=='ja' else en
def text(x,y,s,size=21,color='#14223b',weight=500,anchor='start'):
    return f'<text x="{x}" y="{y}" font-size="{size}" fill="{color}" font-weight="{weight}" text-anchor="{anchor}">{escape(str(s))}</text>'
def lines(x,y,s,lang,width=28,size=20,color='#35506e',step=30,anchor='start'):
    chunks=[]
    for item in (s if isinstance(s,list) else [s]):
        chunks.extend(textwrap.wrap(item,width=width,break_long_words=False) if lang=='en' else [item[i:i+max(1,width//2)] for i in range(0,len(item),max(1,width//2))])
    return ''.join(text(x,y+i*step,c,size,color,anchor=anchor) for i,c in enumerate(chunks))
def rect(x,y,w,h,fill='#fff',stroke='#c4d6eb',r=12): return f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="{r}" fill="{fill}" stroke="{stroke}" stroke-width="2"/>'
def line(x1,y1,x2,y2,color='#58708f',dash=False,width=3):return f'<path d="M{x1},{y1} L{x2},{y2}" fill="none" stroke="{color}" stroke-width="{width}"'+(' stroke-dasharray="7 6"' if dash else '')+'/>'
def arrow(x1,y1,x2,y2,color='#58708f',dash=False):
    import math
    a=math.atan2(y2-y1,x2-x1); n=11
    pts=f'{x2},{y2} {x2-n*math.cos(a-.5)},{y2-n*math.sin(a-.5)} {x2-n*math.cos(a+.5)},{y2-n*math.sin(a+.5)}'
    return line(x1,y1,x2,y2,color,dash)+f'<polygon points="{pts}" fill="{color}"/>'
def circle(x,y,r,fill,stroke='none'): return f'<circle cx="{x}" cy="{y}" r="{r}" fill="{fill}" stroke="{stroke}" stroke-width="2"/>'
def card(x,y,w,h,title,body,lang,color='blue'):
    c=COLORS.get(color,color)
    return rect(x,y,w,h,'#fff',c)+f'<rect x="{x}" y="{y+12}" width="5" height="{h-24}" fill="{c}"/>'+lines(x+20,y+36,title,lang,width=int((w-40)/10),size=22,color=c,step=29)+lines(x+20,y+92,body,lang,width=int((w-40)/10),size=20)
def titleline(s):return text(30,38,s,23,'#23466e',700)
def foot(s,y=392):return text(440,y,s,19,'#4e6583',500,'middle')

def observers(lang):
    t=lambda j,e:label(j,e,lang)
    s=titleline(t('同じ準備から、異なる物理的な継続へ','One preparation; different physical continuations'))
    s+=rect(325,80,230,230,'#132c50','#163658')
    s+=f'<ellipse cx="440" cy="193" rx="98" ry="48" transform="rotate(-24 440 193)" fill="none" stroke="#f8ae59" stroke-width="14" opacity=".9"/>'
    s+=circle(440,190,66,'#06142c','#6b9abc')+text(440,198,t('接合部','Junction'),20,'#e6f4ff',600,'middle')
    s+=circle(110,130,26,'#245edb')+text(110,138,'A',23,'white',700,'middle')
    s+=circle(760,130,26,'#7547bc')+text(760,138,'B',23,'white',700,'middle')
    s+=text(110,87,t('落下する観測者','Infalling observer'),20,anchor='middle')+text(760,87,t('外部の観測者','Exterior observer'),20,anchor='middle')
    s+=arrow(146,137,367,184,COLORS['blue'])+arrow(730,146,554,202,COLORS['purple'],True)
    s+=card(25,220,270,136,t('Aの指定された出力','Specified A output'),t('内向きの継続を許す','Inward continuation allowed'),lang,'blue')
    s+=card(585,220,270,136,t('選ばれたBの出力','Selected B output'),t('全内向きポートの閉鎖が条件','Exterior-only if every inward port closes'),lang,'purple')
    s+=foot(t('模式図：この違いを自然な崩壊から導くことが研究課題','Schematic: obtaining both from natural collapse remains open'),414)
    return s,440

def instrument(lang):
    t=lambda j,e:label(j,e,lang);s=titleline(t('相関をつくる発展と、結果を選ぶ法則','Correlation dynamics and an outcome-selecting rule'))
    s+=card(25,105,240,194,t('通常の発展','Ordinary evolution'),[t('源・環境・反跳を含む','Source, environment, recoil'),t('全体では可逆','Reversible as a whole')],lang,'blue')
    s+=card(315,105,240,194,t('CATの追加仮説','CAT postulate'),[t('受信した荷を選択','Select a received charge'),t('群の間の位相を失う','Remove intergroup phase')],lang,'orange')
    s+=arrow(270,205,306,205)+arrow(560,205,600,122)+arrow(560,205,600,212)+arrow(560,205,600,302)
    for y,c,txt in [(70,'teal',t('結果 z₁','Outcome z₁')),(160,'purple',t('結果 z₂','Outcome z₂')),(250,'gray',t('空の結果も含む','Include empty outcome'))]:
        s+=rect(605,y,250,70,'#fff',COLORS[c])+text(730,y+42,txt,21,COLORS[c],650,'middle')
    s+=foot(t('各枝は代替的な結果。全結果を合計すると総確率は1','Branches are alternatives. Their probabilities sum to one.'),370)
    s+=foot(t('結果の分類を変えても、固定ネットワークの総チャネルは共通','Coarse-graining preserves the fixed network’s total channel.'),405)
    return s,440

def modes(lang):
    t=lambda j,e:label(j,e,lang);s=titleline(t('球面制約の下で、空間モードを数える','Spatial modes under the spherical constraint'))
    for i,(m,nmode,col) in enumerate([(1,0,'red'),(2,1,'teal'),(3,2,'blue')]):
        x=25+290*i;c=COLORS[col];s+=rect(x,75,270,285,'#fff',c)
        s+=text(x+135,115,f'n = 2,  m = {m}',25,c,700,'middle')
        s+=text(x+135,156,t(f'内向き {nmode} モード',f'{nmode} inward '+('mode' if nmode==1 else 'modes')),22,c,600,'middle')
        s+=circle(x+47,225,19,'#b8cee9')+line(x+115,182,x+115,285,'#819ab7',width=6)
        if nmode==0:
            s+=arrow(x+50,246,x+50,310,COLORS['purple'])+text(x+87,314,t('表面へ','Surface'),19,COLORS['purple'])
            s+=text(x+190,230,'×',40,c,700,'middle')
        else:
            for j in range(nmode):
                y=212+42*j;s+=arrow(x+70,y,x+240,y,c)+rect(x+145,y-13,35,26,'#ecf5ff',c,r=4)+text(x+162,y+7,'C',18,c,700,'middle')
        s+=text(x+135,342,f'm − n = {m-2:+d}',21,'#476078',500,'middle')
    s+=foot(t('一つの空間モードでも、未知の内部状態C全体を運べる','One spatial mode can carry the entire unknown internal state C.'),407)
    return s,440

def probabilities(lang,joint=False):
    t=lambda j,e:label(j,e,lang)
    if joint:
        s=titleline(t('同じ源の準備から得た同時確率','Joint probabilities from the common source'))
        s+=text(410,90,t('B：相対電荷 −1','B: m − n = −1'),22,COLORS['purple'],650,'middle')+text(695,90,t('それ以外','Otherwise'),22,COLORS['gray'],650,'middle')
        s+=lines(30,160,t(['A：両端が','実際に吸収'],['A: both ends','actually absorbed']),lang,width=18,size=21)
        s+=lines(30,300,t('それ以外','Otherwise'),lang,width=18,size=21)
        for x,y,val,col in [(275,110,'19.6608%','teal'),(565,110,'11.0592%','blue'),(275,250,'34.0992%','purple'),(565,250,'35.1808%','gray')]:
            s+=rect(x,y,265,112,'#fff',COLORS[col])+text(x+132,y+66,val,32,COLORS[col],700,'middle')
        s+=foot(t('指定された有限模型：r = 0.75、p = 0.64。観測値ではない','Specified finite model: r = 0.75, p = 0.64. Not observations.'),409)
        return s,440
    s=titleline(t('閉鎖の53.76%は、二つの準備の枝の合計','The 53.76% closure rate sums two source branches'))
    for y,title,formula,col in [(80,t('第二パケットがBで暗い','Second packet dark at B'),'0.75 × 0.64 = 0.48','teal'),(210,t('第二パケットがBで明るい','Second packet bright at B'),'0.25 × 0.64 × 0.36 = 0.0576','purple')]:
        s+=rect(25,y,830,110,'#fff',COLORS[col])+text(47,y+36,title,22,COLORS[col],650)+text(47,y+80,formula,27,COLORS[col],700)
    s+=rect(25,350,830,46,'#e4ebf4','#c4d6eb',r=4)
    s+=f'<rect x="25" y="350" width="{830*.48}" height="46" fill="{COLORS["teal"]}"/><rect x="{25+830*.48}" y="350" width="{830*.0576}" height="46" fill="{COLORS["purple"]}"/>'
    s+=text(175,381,'53.76%',25,'white',750)+text(680,381,t('その他 46.24%','Other 46.24%'),20,'#3c5575',600,'middle')
    s+=foot(t('閉鎖した履歴では内向きモードは厳密に0。全試行が閉鎖するわけではない','Closed histories have exactly zero inward modes; not all trials close.'),444)
    return s,478

def receipts(lang):
    t=lambda j,e:label(j,e,lang);s=titleline(t('受信の物理：荷だけでなく、反跳とエネルギーも','Physical reception: charge, recoil, and energy'))
    s+=card(25,95,235,195,t('入射パケット','Incident packet'),t('励起に使うエネルギーを運ぶ','Carries the excitation energy'),lang,'blue')
    s+=arrow(265,190,335,190,COLORS['blue'])
    s+=rect(345,75,480,255,'#eff5fc','#7798bd')+text(585,112,t('複合受信体','Composite receiver'),23,'#274668',700,'middle')
    s+=rect(365,140,205,110,'white',COLORS['orange'])+text(468,179,t('受信端','Receiving end'),21,COLORS['orange'],600,'middle')+text(468,224,'+1',34,COLORS['orange'],700,'middle')
    s+=rect(595,140,205,110,'white',COLORS['purple'])+text(698,179,t('補償端','Compensating end'),21,COLORS['purple'],600,'middle')+text(698,224,'−1',34,COLORS['purple'],700,'middle')
    s+=arrow(490,286,735,286,COLORS['gray'])+text(585,318,t('複合体の反跳','Composite recoil'),20,'#476078',500,'middle')
    s+=foot(t('保存則を満たす吸収過程と、CATの不可逆選択は別の条件','Conserving absorption and CAT’s irreversible selection are separate inputs.'),385)
    return s,420

def history(lang):
    t=lambda j,e:label(j,e,lang);s=titleline(t('占有された全比較で、不一致がゼロになる部分','The common zero space of all occupied comparisons'))
    s+=text(55,105,t('候補の入力','Candidate input'),21,'#25496d',650)
    for j,st in enumerate(['T₁','T₂','T₃']):s+=text(350+j*145,105,st,25,'#25496d',700,'middle')
    for i,vals in enumerate([(0,0,0),(0,1,0),(1,0,1)]):
        y=145+i*66;s+=text(60,y+24,['u','v','w'][i],25,'#25496d',700)
        for j,val in enumerate(vals):
            c=COLORS['teal'] if val==0 else COLORS['red'];s+=rect(305+j*145,y,90,44,'#fff',c,r=6)+text(350+j*145,y+30,'0' if val==0 else '≠ 0',23,c,700,'middle')
        s+=arrow(705,y+22,750,y+22,COLORS['teal'] if i==0 else COLORS['purple'])+text(772,y+30,t('内向き','Inward') if i==0 else t('表面','Surface'),18,COLORS['teal'] if i==0 else COLORS['purple'])
    s+=foot(t('線形代数の模式図。正の項の和では不一致同士が相殺しない','Linear-algebra schematic: positive mismatch terms cannot cancel.'),393)
    return s,425

def deadline(lang):
    t=lambda j,e:label(j,e,lang);s=titleline(t('10太陽質量の指定例：異なる時計を分ける','Specified 10-solar-mass example: keep the clocks separate'))
    for x,col,heading,num,body in [(25,'blue',t('Aの固有時計','A’s proper clock'),'20.66 μs',t('1.2 rₛ から地平面 rₛ まで','From 1.2 rₛ to the horizon rₛ')),(455,'orange',t('静止受信機の時計','Stationary receiver clock'),'1.003 μs',t('1.01 rₛ で信号がAに先行','Signal lead over A at 1.01 rₛ'))]:
        c=COLORS[col];s+=rect(x,85,400,260,'#fff',c)+text(x+200,127,heading,23,c,650,'middle')
        s+=circle(x+75,215,43,'#eff4fc',c)+line(x+75,215,x+75,184,c)+line(x+75,215,x+103,229,c)
        s+=text(x+238,210,num,31,c,700,'middle')+lines(x+238,252,body,lang,width=25,size=19,anchor='middle')
    s+=foot(t('異なる終点を測る時間。差し引きや同一時計での比較はしない','These intervals have different endpoints; do not subtract them.'),391)
    s+=foot(t('到着の余裕だけでは、荷の書き込み成功は保証されない','An arrival margin does not itself establish successful charge writing.'),425)
    return s,458

def recovery(lang):
    t=lambda j,e:label(j,e,lang);s=titleline(t('一つの未知量子ビットを、担体の旗を使って復号する','Decode one unknown qubit using its carrier flag'))
    s+=circle(100,130,32,'#f1edfa',COLORS['purple'])+text(100,139,'R',26,COLORS['purple'],700,'middle')+text(100,82,t('触らない参照系','Untouched reference'),19,'#476078',500,'middle')
    s+=line(100,165,100,230,COLORS['purple'],True)+circle(100,267,32,'#e7f2ff',COLORS['blue'])+text(100,275,'C',26,COLORS['blue'],700,'middle')
    s+=text(100,327,t('単一の入力','Single input'),20,'#476078',500,'middle')
    for y,c,name,weight in [(65,'teal',t('光子対','Photon pair'),'1/2'),(175,'purple',t('重力子対','Graviton pair'),'1/3'),(285,'orange',t('残留コア','Residual core'),'1/6')]:
        s+=arrow(140,267,277,y+40,COLORS[c])+rect(285,y,295,82,'#fff',COLORS[c])+text(305,y+34,name,22,COLORS[c],650)+text(550,y+57,weight,25,COLORS[c],700,'end')
        s+=arrow(585,y+41,680,221,COLORS[c])
    s+=rect(685,155,170,150,'#e9f4fa',COLORS['teal'])+lines(770,192,[t('旗で復号','Decode by flag'),t('位相も保存','Preserve phase')],lang,width=16,size=20,color=COLORS['teal'],anchor='middle')
    s+=foot(t('3個の複製ではなく、代替的な担体。必要な担体へのアクセスが条件','Alternative carriers, not three clones. Access to the required carriers is assumed.'),414)
    return s,445

def scope(lang):
    t=lambda j,e:label(j,e,lang);s=titleline(t('10個の行列成分と、行列の大きさNを区別する','Distinguish ten matrix components from matrix size N'))
    for i in range(10):
        x=25+i*84;s+=rect(x,75,72,60,'#edf3ff',COLORS['blue'],r=5)+text(x+36,113,f'X{i}',22,COLORS['blue'],650,'middle')
    s+=card(25,175,390,177,t('実際に計算した範囲','Calculated sector'),[t('行列サイズ・時計・ポートを指定','Choose rank, clock, and ports'),t('散乱ブロック全体を用いる','Use full scattering blocks')],lang,'teal')
    s+=card(465,175,390,177,t('次の構成課題','Open construction'),[t('異なるランクと時計を対応づける','Identify preparations across sectors'),t('整合する確率を定める','Define consistent probabilities')],lang,'purple')
    s+=arrow(421,264,457,264,COLORS['purple'],True)
    s+=foot(t('有限時計の終端と、行列ランクの無限極限は別の操作','Ending a finite clock chain is not taking a matrix-rank limit.'),401)
    return s,435

def geometry(lang,ladder=False):
    t=lambda j,e:label(j,e,lang);s=titleline(t('伝播が示す計量と、重力方程式の成立を分ける','Separate a propagation metric from the gravity equations'))
    cards=[(25,'blue',t('行列背景','Matrix background'),t('物質波の入力','Matter-wave input')),(315,'teal',t('波の主部 H','Wave principal part H'),t('伝播と潮汐を測る','Probe propagation and tides')),(605,'purple',t('有効計量 g','Effective metric g'),t('一般の場の方程式は別検査','Test field equations separately'))]
    for x,c,h,b in cards:s+=card(x,80,250,156,h,b,lang,c)
    s+=arrow(280,156,305,156)+arrow(570,156,595,156)
    s+=text(585,258,'det H ≠ 0;  d = 4',18,COLORS['purple'],600,'middle')
    if ladder:
        s+=rect(25,275,830,110,'#fff',COLORS['orange'])+text(50,315,t('特定の真空波：Tr K = 0 を満たす部分','Specified vacuum waves: select the family with Tr K = 0'),22,COLORS['orange'],650)
        s+=text(50,355,t('一般物質・普遍的結合・安定性は、さらに必要','General matter, universal coupling, and stability remain further tests.'),20)
        return s,420
    s+=text(30,286,t('同じ過去と向きを保持した二つの継続','Two continuations retaining the same past and orientation'),21,'#294d73',650)
    s+=rect(25,310,370,112,'#eef6fa','#9ac5d1')+lines(47,348,[t('0°・90°の腕：復帰時刻は一致','0° / 90° arms: return times agree'),t('限られた一致だけでは不十分','A few agreements do not fix a metric')],lang,width=35,size=19)
    s+=rect(425,310,430,112,'#f3effc','#b49ad8')+text(450,350,t('45°の腕','45° arm'),20,COLORS['purple'],650)+text(450,390,'0.33301   /   0.30801',27,COLORS['purple'],700)
    s+=foot(t('規格化された波の単位。単一の当てはめに必要な許容差は最低0.01250','Normalized wave units; minimum common-fit tolerance: 0.01250.'),466)
    return s,500

def readout(lang):
    t=lambda j,e:label(j,e,lang);s=titleline(t('900試行の設計：まず較正し、合格した場合だけ判定','A 900-trial design: qualify first, then decide'))
    entries=[('200',t('吸収の較正','Absorption'), 'blue'),('300',t('正の参照入力','Positive reference'),'teal'),('300',t('負の参照入力','Negative reference'),'purple'),('100',t('信号の試行','Signal trials'),'orange')]
    for i,(num,lab,c) in enumerate(entries):
        x=25+i*215;s+=rect(x,80,195,128,'#fff',COLORS[c])+text(x+97,129,num,34,COLORS[c],700,'middle')+lines(x+97,171,lab,lang,width=20,size=19,anchor='middle')
    s+=text(30,254,t('色の帯：較正に合格した場合の許容範囲','Colored bands: allowed ranges after qualification'),20,'#294d73',650)
    s+=line(260,370,825,370,'#7890aa',width=2)
    for x,st in [(260,'0'),(542.5,'0.5'),(825,'1')]:s+=text(x,400,st,19,'#476078',500,'middle')
    for y,val,lab,c in [(280,.659582,t('CAT 上限','CAT upper bound'),'purple'),(330,.970227,t('通常反転 下限','Ordinary lower bound'),'teal')]:
        x0=260 if c=='purple' else 260+565*val
        width=565*val if c=='purple' else 565*(1-val)
        s+=text(30,y+22,lab,19,COLORS[c],650)+rect(260,y,565,31,'#e8edf4','#d3dfed',r=3)
        s+=f'<rect x="{x0}" y="{y}" width="{width}" height="31" fill="{COLORS[c]}" rx="3"/>'+line(260+565*val,y-4,260+565*val,y+35,COLORS[c],width=3)
        s+=text(275,y+23,('≤ ' if c=='purple' else '≥ ')+f'{val:.6f}',20,'white' if c=='purple' else '#234b68',700)
    s+=foot(t('独立な装置誤差の上限を仮定した設計。重力装置での測定値ではない','Design with independent hardware-error bounds; not gravitational measurements.'),446)
    return s,480

def vacua(lang):
    t=lambda j,e:label(j,e,lang);s=titleline(t('限定したフラックス集合を、異なる条件で絞る','Apply different filters within a restricted flux ensemble'))
    items=[('48,055,489',t('偶数ISDフラックス','Even ISD fluxes'),'blue'),('20,597',t('原始的(2,1)条件','Primitive (2,1) condition'),'teal'),('115',t('双対性で同値を除く','Duality orbits'),'purple'),('49',t('10複素変数の線形固定','Linear fixing: 10 complex variables'),'orange'),('41',t('O3荷を飽和','O3 charge saturation'),'red')]
    for i,(val,desc,c) in enumerate(items):
        y=70+i*75;s+=rect(25,y,830,62,'#fff',COLORS[c],r=6)+text(50,y+42,val,27,COLORS[c],700)+text(350,y+40,desc,21,'#35506e',550)
    s+=foot(t('全CAT真空の数ではない。安定性・現実の物質・半径の固定は別問題','Not a count of all CAT vacua. Stability, realistic matter, and radii are separate.'),485)
    return s,515

def testsmap(lang):
    t=lambda j,e:label(j,e,lang);s=titleline(t('何を測るかで分ける、条件付きの検証','Conditional tests, grouped by what is measured'))
    s+=card(25,90,270,250,t('実験室','Laboratory'),[t('全系の反転と位相','Full inverse and phase'),t('較正された吸収・読出し','Calibrated absorption/readout'),t('通常の損失を制限','Bound ordinary losses')],lang,'blue')
    s+=card(305,90,270,250,t('星と高密度天体','Stars and compact objects'),[t('潮汐・偏光・干渉','Tides, polarization, fringes'),t('受信割合を独立に制限','Constrain the write fraction'),t('背景の縮退を管理','Control background degeneracies')],lang,'purple')
    s+=card(585,90,270,250,t('宇宙論と物質の力','Cosmology and matter forces'),[t('距離・膨張・組成依存性','Distance, expansion, composition'),t('指定した枝を検査','Test a specified branch'),t('全真空への一般化はしない','No all-vacua inference')],lang,'teal')
    s+=foot(t('観測で一つの枝を除外することと、CATを検出することは異なる','Excluding a branch is different from detecting CAT.'),395)
    return s,430

def actions(lang):
    t=lambda j,e:label(j,e,lang);s=titleline(t('候補を比べる：同じ静的な力だけでは決まらない','Compare mechanisms beyond the same static force'))
    data=[('blue',t('媒介する場','Mediator field'),[t('独立した伝播をもつか','Does an independent mode propagate?'),t('境界条件も指定する','Specify boundary conditions')]),('orange',t('有限の減衰','Finite damping'),[t('確率を小さくできる','Can reduce a probability'),t('一般に厳密な零にはしない','Does not generically make it zero')]),('purple',t('接触での制約','Contact constraint'),[t('許される経路を変える','Changes the allowed routes'),t('実際の受信が必要','Requires a physical receipt')])]
    for i,(c,h,b) in enumerate(data):s+=card(25+285*i,90,260,254,h,b,lang,c)
    s+=foot(t('CATの選択基準は、指定した内向き経路を厳密に閉じられるか','CAT’s criterion: can the specified inward route close exactly?'),397)
    return s,432

def clock(lang):
    t=lambda j,e:label(j,e,lang);s=titleline(t('物質の交換を、時計の読みとして使う','Use a material exchange as a clock reading'))
    for i in range(5):
        x=55+i*165;s+=circle(x,135,28,'#edf4ff',COLORS['blue'])+text(x,143,f'q{i}',22,COLORS['blue'],700,'middle')
        if i<4:s+=arrow(x+35,135,x+125,135,COLORS['blue'])
    s+=text(825,143,t('終端','End'),20,COLORS['gray'],550,'middle')
    s+=card(25,205,390,169,t('その時計を読む物質波','Matter waves read the clock'),t('伝播・偏光・潮汐を比較する','Compare propagation, polarization, and tides'),lang,'teal')
    s+=card(465,205,390,169,t('重なりで照合する記録','Records compared on overlaps'),t('共有できる範囲で時空の地図を作る','Build a spacetime map where records agree'),lang,'purple')
    s+=arrow(420,290,456,290)
    s+=foot(t('時計の準備は入力。すべての時計を統合する規則は未完成','Preparing the clock is an input; unifying all clocks remains open.'),425)
    return s,458

def generalgeometry(lang):
    t=lambda j,e:label(j,e,lang);s=titleline(t('一つの滑らかな例から、現実の宇宙までの距離','From a smooth example to a viable universe'))
    for i,(c,h,body) in enumerate([('teal',t('折り返す解','A turning solution'),[t('特異点を避ける例','An example avoiding a singularity'),t('出口の物質状態も追う','Track the outgoing matter state')]),('purple',t('真空の候補','Candidate vacuum'),[t('幾何やフラックスを区別','Distinguish geometry and flux'),t('安定性の検査が必要','Stability needs testing')]),('orange',t('物理的な尺度','Physical scales'),[t('共通の半径は自動で決まらない','A common radius is not automatic'),t('粒子・定数も未導出','Particles and constants remain open')])]):s+=card(25+285*i,85,260,265,h,body,lang,c)
    s+=foot(t('それぞれ異なる問い。前の段階の成功が次を保証するわけではない','These are separate questions; success at one does not settle the next.'),402)
    return s,438

def echoes(lang):
    t=lambda j,e:label(j,e,lang);s=titleline(t('「戻る」という言葉が指す、三つの異なる量','Three different meanings of “return”'))
    entries=[('teal',t('内向き経路','Inward route'),[t('許されるモードの数','Count allowed spatial modes'),t('閉鎖はこの指定経路の零','Closure is zero in this port')]),('purple',t('量子状態の帰還','Quantum-state return'),[t('位相も含め元に戻る確率','Return the state, including phase'),t('通常の環境損失も区別','Separate ordinary environment loss')]),('orange',t('天体のエコー','Astrophysical echo'),[t('遅れて届く波の成分','A delayed component of a wave'),t('反射率と伝播が別途必要','Needs reflectivity and propagation')])]
    for i,(c,h,b) in enumerate(entries):s+=card(25+285*i,85,260,260,h,b,lang,c)
    s+=foot(t('経路の閉鎖だけから、エコーの強さや量子帰還率は決まらない','Closure alone fixes neither an echo amplitude nor a quantum return rate.'),399)
    return s,435

def evidence(lang):
    t=lambda j,e:label(j,e,lang);s=titleline(t('確かめたことを、三つの水準に分ける','Three distinct levels of evidence'))
    for i,(c,h,b) in enumerate([('teal',t('条件付きの数学','Conditional mathematics'),[t('仮定の下で命題を確認','Check statements given inputs'),t('Lean・代数・数値比較','Lean, algebra, numerical checks')]),('blue',t('準備を指定した模型','Specified model preparations'),[t('源・荷・経路・復号を計算','Calculate source, charge, routing and decoding'),t('成功例と失敗例を記録','Record successes and failures')]),('orange',t('自然界での実現','Realization in nature'),[t('自然崩壊と重力装置','Natural collapse and apparatus'),t('まだ実証されていない','Not yet demonstrated')])]):s+=card(25+285*i,85,260,270,h,b,lang,c)
    s+=foot(t('計算の再現性は重要な証拠だが、自然界での実現の証明ではない','Reproducibility matters; it does not establish physical realization.'),406)
    return s,440

MAP={
 'expert-observer-domains':observers,'general-observers':observers,
 'expert-history-instrument':instrument,'student-channel':instrument,'general-records':instrument,
 'expert-closure-count':modes,'student-domain':modes,'general-route':modes,
 'expert-joint-probabilities':lambda l:probabilities(l,True),'student-probability':probabilities,
 'student-current':receipts,'student-history':history,'student-deadline':deadline,
 'student-recovery':recovery,'general-source':recovery,'student-scope':scope,
 'student-geometry':geometry,'expert-geometry-ladder':lambda l:geometry(l,True),
 'expert-readout-design':readout,'expert-vacuum-constraints':vacua,'expert-tests-map':testsmap,
 'general-actions':actions,'general-clock':clock,'general-geometry':generalgeometry,
 'general-echo':echoes,'general-evidence':evidence,
}

CAPTIONS={
 'observers':('二つの観測者の記述','Two observer descriptions','接合部で指定した物理条件による比較。図の円は実測された天体像ではありません。','Comparison under stated junction conditions; the circle is not an observed astronomical image.'),
 'instrument':('通常の相関と、追加された選択','Ordinary correlations and additional selection','可逆な発展と、そこから選ばれる記録を分けて読みます。受信済みの結果 z は、図の後に続くポート操作 W を制御します。','Separate reversible dynamics from the selected records. The received outcome z controls the later port operation W, beyond the stages drawn here.'),
 'modes':('条件付きで、経路が厳密に消える','Exact closure under a stated constraint','異なる次数の三つのセクター。内部量子状態の次元と空間モード数は別です。複数の線は許される空間モードであり、未知状態 C の複製ではありません。','Three degree sectors. Internal-state dimension and spatial-mode count are distinct. Multiple lines denote allowed spatial modes, not copies of the unknown state C.'),
 'probabilities':('閉鎖割合の内訳','Anatomy of a closure probability','指定した源と吸収率での計算値です。観測データを示しているわけではありません。','Calculated for the stated source and absorption probability, not observed data.'),
 'joint_probabilities':('同じ準備の共同分布','Joint distribution from one preparation','A の事象は両端で実際に吸収された場合で、空の二つの記録の一致を含みません。B の事象は相対電荷 m_B − n_B = −1、すなわち指定ポートが閉鎖する場合です。r = 0.75、p = 0.64 の計算値で、観測データではありません。','The A event requires actual absorption at both ends; equality of two empty records does not qualify. The B event is relative charge m_B − n_B = −1, which closes the specified port. Values are calculated at r = 0.75 and p = 0.64, not observed data.'),
 'receipts':('選択の前に、物理的な受信が要る','A physical receipt must precede selection','エネルギー・運動量・補償荷を含む過程を指定して初めて、追加の法則を検査できます。','Specify energy, momentum, and compensating charge before testing an added law.'),
 'history':('共通の零空間が残る','The common kernel survives','説明のための線形代数の図で、追加のCAT数値実験ではありません。','A linear-algebra illustration, not an additional numerical CAT experiment.'),
 'deadline':('二つの固有時計を混同しない','Do not mix the two proper clocks','主論文の特定の10太陽質量例。二つの時間は測る終点も異なります。','The paper’s specified ten-solar-mass example; the intervals have different endpoints.'),
 'recovery':('情報回復は、位相ともつれを保つこと','Recovery preserves phase and entanglement','指定された閉鎖履歴の例。重みの合計だけで量子回復が証明されるわけではありません。','A specified closed-history example; adding probabilities is not itself a proof of quantum recovery.'),
 'scope':('固定したセクターと、全体理論の構成','A fixed sector and completion of the theory','非摂動的な有限計算と、ランク・時計を横断した整合性の課題を分けます。','Distinguish finite nonperturbative calculations from consistency across ranks and clocks.'),
 'geometry':('物質が測る幾何','Geometry measured by matter','ここで示す H から計量 g への構成は、非退化な H と4次元を前提とします。物質波の伝播から読んだ幾何と、一般の重力方程式の成立は別々に検査します。','The displayed construction from H to the metric g assumes nondegenerate H in four dimensions. Probe geometry and general gravitational dynamics require separate checks.'),
 'readout':('較正条件付きの実験設計','An experiment conditional on calibration','目標吸収率は p = 8/9。全許容状態と付随する旗に一様な全回路誤差 Δ ≤ 0.01、および暗計数確率 d ≤ 0.01 を、較正とは独立に仮定します。移送・逆操作などもこの誤差枠に含む、未実施の設計です。','The target absorption probability is p = 8/9. Independently of the calibration, the design assumes full-circuit error Δ ≤ 0.01 uniformly over all admitted states and attached flags, and dark-click probability d ≤ 0.01. This prospective, unperformed design includes transfer and inversion errors within that envelope.'),
 'vacua':('限定した集合での数え上げ','Counting within a restricted ensemble','指定した正方トーラス orientifold で、結合と tadpole 上限を固定した計数です。これらの整数を、安定した全真空の個数や現実の宇宙の選択確率とは解釈しません。','Counts for the specified square-torus orientifold at fixed coupling and tadpole bound. These integers are not counts of all stable vacua or probabilities for our universe.'),
 'testsmap':('指定した枝を試す観測','Observations test specified branches','通常の吸収や背景幾何による縮退を制御して、初めて各予測を比較できます。','Control ordinary absorption and background geometry before comparing predictions.'),
 'actions':('作用を選ぶための比較','Comparing candidate interactions','静的な力の一致、有限の減衰、物理的な出力空間の変更は同じ条件ではありません。','Equal static forces, finite damping, and changed output spaces are different conditions.'),
 'clock':('物質の時計から、共通の地図へ','From a material clock to a shared map','時計と源を準備し、比較可能な記録が整合する範囲で時空を再構成します。','Prepare a clock and source, then compare records where a shared geometry is consistent.'),
 'generalgeometry':('解・真空・尺度を区別する','Distinguish solutions, vacua, and scales','一般的な特異点解消、安定真空、観測された粒子・定数の導出は未解決です。','Generic singularity resolution, a stable vacuum, and observed particles/constants remain open.'),
 'echoes':('三つの「帰還」を分ける','Separate three kinds of return','空間経路、量子状態、天体の波という、異なる測定対象を表しています。','The measured objects differ: a spatial route, a quantum state, and an astronomical wave.'),
 'evidence':('数学から自然界へ','From mathematics to nature','確認できた水準を示し、未完成の部分も研究課題として明示します。','State the level supported by the checks and identify the remaining research tasks.'),
}

def figure(fid,lang):
    if fid not in MAP: raise KeyError('Missing figure specification: '+fid)
    fun=MAP[fid]; body,height=fun(lang)
    key=fun.__name__
    if fid=='expert-joint-probabilities':key='joint_probabilities'
    if fid=='expert-geometry-ladder':key='geometry'
    cap=CAPTIONS[key];heading=cap[0 if lang=='ja' else 1];desc=cap[2 if lang=='ja' else 3]
    title_id=f'{fid}-{lang}-title'
    svg=f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 880 {height}" role="img" aria-labelledby="{title_id}"><title id="{title_id}">{escape(heading+". "+desc)}</title>{body}</svg>'
    hint=label('小さな画面では図を横にスクロールできます。','On a small screen, scroll the diagram horizontally.',lang)
    return f'<figure class="diagram" id="figure-{fid}"><div class="diagram-scroll" tabindex="0" aria-label="{escape(heading)}">{svg}</div><div class="scroll-hint">{hint}</div><figcaption><strong>{escape(heading)}</strong>{escape(desc)}</figcaption></figure>'
