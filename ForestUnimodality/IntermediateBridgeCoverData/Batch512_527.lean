import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band512 : Band CellKey where
  qlo := (99/179)
  qhi := (5/9)
  mlo := (81/5)
  mhi := (11118970011585422701996853242851/250000000000000000000000000000)
  cells := [(59,205),(99,162),(130,217)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 104

theorem band512_checked : band512.check rectangle=true := by decide +kernel
#print axioms band512_checked

def band513 : Band CellKey where
  qlo := (99/179)
  qhi := (5/9)
  mlo := (108/5)
  mhi := (11118970011585422701996853242851/250000000000000000000000000000)
  cells := [(80,199),(99,162),(130,217)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 104

theorem band513_checked : band513.check rectangle=true := by decide +kernel
#print axioms band513_checked

def band514 : Band CellKey where
  qlo := (99/179)
  qhi := (5/9)
  mlo := (261/10)
  mhi := (11118970011585422701996853242851/250000000000000000000000000000)
  cells := [(99,162),(130,217)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 104

theorem band514_checked : band514.check rectangle=true := by decide +kernel
#print axioms band514_checked

def band515 : Band CellKey where
  qlo := (99/179)
  qhi := (5/9)
  mlo := (171/5)
  mhi := (11118970011585422701996853242851/250000000000000000000000000000)
  cells := [(130,217)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 104

theorem band515_checked : band515.check rectangle=true := by decide +kernel
#print axioms band515_checked

def band516 : Band CellKey where
  qlo := (5/9)
  qhi := (116/207)
  mlo := (16060344827586206896551724137931/1000000000000000000000000000000)
  mhi := (44191329445710165215338647635999/1000000000000000000000000000000)
  cells := [(59,206),(99,163),(130,218)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 105

theorem band516_checked : band516.check rectangle=true := by decide +kernel
#print axioms band516_checked

def band517 : Band CellKey where
  qlo := (5/9)
  qhi := (116/207)
  mlo := (21413793103448275862068965517241/1000000000000000000000000000000)
  mhi := (44191329445710165215338647635999/1000000000000000000000000000000)
  cells := [(80,200),(99,163),(130,218)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 105

theorem band517_checked : band517.check rectangle=true := by decide +kernel
#print axioms band517_checked

def band518 : Band CellKey where
  qlo := (5/9)
  qhi := (116/207)
  mlo := (26767241379310344827586206896551/1000000000000000000000000000000)
  mhi := (44191329445710165215338647635999/1000000000000000000000000000000)
  cells := [(99,163),(130,218)]
  lowerOrder := 99
  orderCap := 129
  rank := 30
  parentStrip := 105

theorem band518_checked : band518.check rectangle=true := by decide +kernel
#print axioms band518_checked

def band519 : Band CellKey where
  qlo := (5/9)
  qhi := (116/207)
  mlo := (6781034482758620689655172413793/200000000000000000000000000000)
  mhi := (44191329445710165215338647635999/1000000000000000000000000000000)
  cells := [(130,218)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 105

theorem band519_checked : band519.check rectangle=true := by decide +kernel
#print axioms band519_checked

def band520 : Band CellKey where
  qlo := (116/207)
  qhi := (13/23)
  mlo := (3980769230769230769230769230769/250000000000000000000000000000)
  mhi := (44003707473682260174411173995509/1000000000000000000000000000000)
  cells := [(59,207),(99,164),(130,219)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 106

theorem band520_checked : band520.check rectangle=true := by decide +kernel
#print axioms band520_checked

def band521 : Band CellKey where
  qlo := (116/207)
  qhi := (13/23)
  mlo := (21230769230769230769230769230769/1000000000000000000000000000000)
  mhi := (44003707473682260174411173995509/1000000000000000000000000000000)
  cells := [(80,201),(99,164),(130,219)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 106

theorem band521_checked : band521.check rectangle=true := by decide +kernel
#print axioms band521_checked

def band522 : Band CellKey where
  qlo := (116/207)
  qhi := (13/23)
  mlo := (26538461538461538461538461538461/1000000000000000000000000000000)
  mhi := (44003707473682260174411173995509/1000000000000000000000000000000)
  cells := [(99,164),(130,219)]
  lowerOrder := 99
  orderCap := 129
  rank := 30
  parentStrip := 106

theorem band522_checked : band522.check rectangle=true := by decide +kernel
#print axioms band522_checked

def band523 : Band CellKey where
  qlo := (116/207)
  qhi := (13/23)
  mlo := (69/2)
  mhi := (44003707473682260174411173995509/1000000000000000000000000000000)
  cells := [(130,219)]
  lowerOrder := 130
  orderCap := 169
  rank := 39
  parentStrip := 106

theorem band523_checked : band523.check rectangle=true := by decide +kernel
#print axioms band523_checked

def band524 : Band CellKey where
  qlo := (13/23)
  qhi := (21/37)
  mlo := (7928571428571428571428571428571/500000000000000000000000000000)
  mhi := (11002494483456943760757069942117/250000000000000000000000000000)
  cells := [(59,208),(99,165),(130,220)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 107

theorem band524_checked : band524.check rectangle=true := by decide +kernel
#print axioms band524_checked

def band525 : Band CellKey where
  qlo := (13/23)
  qhi := (21/37)
  mlo := (21142857142857142857142857142857/1000000000000000000000000000000)
  mhi := (11002494483456943760757069942117/250000000000000000000000000000)
  cells := [(80,202),(80,203),(80,204),(80,205),(80,206),(99,165),(130,220)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 107

theorem band525_checked : band525.check rectangle=true := by decide +kernel
#print axioms band525_checked

def band526 : Band CellKey where
  qlo := (13/23)
  qhi := (21/37)
  mlo := (26428571428571428571428571428571/1000000000000000000000000000000)
  mhi := (11002494483456943760757069942117/250000000000000000000000000000)
  cells := [(99,165),(130,220)]
  lowerOrder := 99
  orderCap := 129
  rank := 30
  parentStrip := 107

theorem band526_checked : band526.check rectangle=true := by decide +kernel
#print axioms band526_checked

def band527 : Band CellKey where
  qlo := (13/23)
  qhi := (21/37)
  mlo := (17178571428571428571428571428571/500000000000000000000000000000)
  mhi := (11002494483456943760757069942117/250000000000000000000000000000)
  cells := [(130,220)]
  lowerOrder := 130
  orderCap := 169
  rank := 39
  parentStrip := 107

theorem band527_checked : band527.check rectangle=true := by decide +kernel
#print axioms band527_checked

end ForestUnimodality.IntermediateBridgeCoverData

