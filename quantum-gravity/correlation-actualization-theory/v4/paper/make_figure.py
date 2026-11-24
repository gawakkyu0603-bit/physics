"""Draw the conditional branches in the article; write a vector PDF beside this file."""
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

plt.rcParams.update({"font.family":"DejaVu Sans","pdf.fonttype":42})
fig,ax=plt.subplots(figsize=(7.4,3.15))
ax.set(xlim=(0,10),ylim=(0,4.4));ax.axis("off")
navy="#22374d";teal="#165f58";rust="#854820";muted="#536475"

def box(x,y,w,h,heading,detail,colour,fill):
    ax.add_patch(FancyBboxPatch((x,y),w,h,boxstyle="round,pad=0.04,rounding_size=0.09",
                               edgecolor=colour,facecolor=fill,linewidth=1.05))
    ax.text(x+w/2,y+h*.68,heading,ha="center",va="center",color=colour,fontsize=10.5,weight="bold")
    ax.text(x+w/2,y+h*.29,detail,ha="center",va="center",color=navy,fontsize=8.5)

def arrow(a,b,dashed=False):
    ax.add_patch(FancyArrowPatch(a,b,arrowstyle="-|>",mutation_scale=12,
                                linewidth=1.1,color=muted,linestyle="--" if dashed else "-"))

box(2.05,3.38,5.9,.79,"One preparation of matter and fields",
    "Ordinary interactions correlate A, its surroundings and the receivers.",navy,"#f3f6fa")
arrow((4.0,3.33),(2.48,2.68),True);arrow((6.0,3.33),(7.52,2.68),True)
box(.25,1.83,4.45,.80,"A receives matching charges","Relative degree  m − n = 0",teal,"#eef7f4")
box(5.30,1.83,4.45,.80,"B receives a signed mismatch","Relative degree  m − n = −1",rust,"#fbf2ea")
arrow((2.48,1.78),(2.48,1.13));arrow((7.52,1.78),(7.52,1.13))
box(.25,.22,4.45,.86,"One inward spatial mode","Any payload state can continue through this link.",teal,"#eef7f4")
box(5.30,.22,4.45,.86,"No inward spatial mode","The surface carries the payload in this sector.",rust,"#fbf2ea")
fig.subplots_adjust(left=.01,right=.99,top=.995,bottom=.005)
fig.savefig(Path(__file__).with_name("fig-route.pdf"),metadata={"Creator":"CAT reviewer archive","CreationDate":None,"ModDate":None})
plt.close(fig)

