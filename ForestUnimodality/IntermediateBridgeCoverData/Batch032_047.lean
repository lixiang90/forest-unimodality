import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band032 : Band CellKey where
  qlo := (13/42)
  qhi := (20/63)
  mlo := (189/8)
  mhi := (1071/16)
  cells := [(59,8),(99,8),(130,8)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 8

theorem band032_checked : band032.check rectangle=true := by decide +kernel
#print axioms band032_checked

def band033 : Band CellKey where
  qlo := (13/42)
  qhi := (20/63)
  mlo := (63/2)
  mhi := (1071/16)
  cells := [(80,8),(99,8),(130,8)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 8

theorem band033_checked : band033.check rectangle=true := by decide +kernel
#print axioms band033_checked

def band034 : Band CellKey where
  qlo := (13/42)
  qhi := (20/63)
  mlo := (315/8)
  mhi := (1071/16)
  cells := [(99,8),(130,8)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 8

theorem band034_checked : band034.check rectangle=true := by decide +kernel
#print axioms band034_checked

def band035 : Band CellKey where
  qlo := (13/42)
  qhi := (20/63)
  mlo := (2079/40)
  mhi := (1071/16)
  cells := [(130,8)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 8

theorem band035_checked : band035.check rectangle=true := by decide +kernel
#print axioms band035_checked

def band036 : Band CellKey where
  qlo := (20/63)
  qhi := (41/126)
  mlo := (11524390243902439024390243902439/500000000000000000000000000000)
  mhi := (65304878048780487804878048780487/1000000000000000000000000000000)
  cells := [(59,9),(99,9),(130,9)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 9

theorem band036_checked : band036.check rectangle=true := by decide +kernel
#print axioms band036_checked

def band037 : Band CellKey where
  qlo := (20/63)
  qhi := (41/126)
  mlo := (3073170731707317073170731707317/100000000000000000000000000000)
  mhi := (65304878048780487804878048780487/1000000000000000000000000000000)
  cells := [(80,9),(99,9),(130,9)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 9

theorem band037_checked : band037.check rectangle=true := by decide +kernel
#print axioms band037_checked

def band038 : Band CellKey where
  qlo := (20/63)
  qhi := (41/126)
  mlo := (38414634146341463414634146341463/1000000000000000000000000000000)
  mhi := (65304878048780487804878048780487/1000000000000000000000000000000)
  cells := [(99,9),(130,9)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 9

theorem band038_checked : band038.check rectangle=true := by decide +kernel
#print axioms band038_checked

def band039 : Band CellKey where
  qlo := (20/63)
  qhi := (41/126)
  mlo := (50707317073170731707317073170731/1000000000000000000000000000000)
  mhi := (65304878048780487804878048780487/1000000000000000000000000000000)
  cells := [(130,9)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 9

theorem band039_checked : band039.check rectangle=true := by decide +kernel
#print axioms band039_checked

def band040 : Band CellKey where
  qlo := (41/126)
  qhi := (1/3)
  mlo := (45/2)
  mhi := (255/4)
  cells := [(59,10),(99,10),(130,10)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 10

theorem band040_checked : band040.check rectangle=true := by decide +kernel
#print axioms band040_checked

def band041 : Band CellKey where
  qlo := (41/126)
  qhi := (1/3)
  mlo := (30/1)
  mhi := (255/4)
  cells := [(80,10),(99,10),(130,10)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 10

theorem band041_checked : band041.check rectangle=true := by decide +kernel
#print axioms band041_checked

def band042 : Band CellKey where
  qlo := (41/126)
  qhi := (1/3)
  mlo := (75/2)
  mhi := (255/4)
  cells := [(99,10),(130,10)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 10

theorem band042_checked : band042.check rectangle=true := by decide +kernel
#print axioms band042_checked

def band043 : Band CellKey where
  qlo := (41/126)
  qhi := (1/3)
  mlo := (99/2)
  mhi := (255/4)
  cells := [(130,10)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 10

theorem band043_checked : band043.check rectangle=true := by decide +kernel
#print axioms band043_checked

def band044 : Band CellKey where
  qlo := (1/3)
  qhi := (29/85)
  mlo := (2747844827586206896551724137931/125000000000000000000000000000)
  mhi := (62284482758620689655172413793103/1000000000000000000000000000000)
  cells := [(59,11),(99,11),(130,11)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 11

theorem band044_checked : band044.check rectangle=true := by decide +kernel
#print axioms band044_checked

def band045 : Band CellKey where
  qlo := (1/3)
  qhi := (29/85)
  mlo := (29310344827586206896551724137931/1000000000000000000000000000000)
  mhi := (62284482758620689655172413793103/1000000000000000000000000000000)
  cells := [(80,11),(99,11),(130,11)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 11

theorem band045_checked : band045.check rectangle=true := by decide +kernel
#print axioms band045_checked

def band046 : Band CellKey where
  qlo := (1/3)
  qhi := (29/85)
  mlo := (36637931034482758620689655172413/1000000000000000000000000000000)
  mhi := (62284482758620689655172413793103/1000000000000000000000000000000)
  cells := [(99,11),(130,11)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 11

theorem band046_checked : band046.check rectangle=true := by decide +kernel
#print axioms band046_checked

def band047 : Band CellKey where
  qlo := (1/3)
  qhi := (29/85)
  mlo := (24181034482758620689655172413793/500000000000000000000000000000)
  mhi := (62284482758620689655172413793103/1000000000000000000000000000000)
  cells := [(130,11)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 11

theorem band047_checked : band047.check rectangle=true := by decide +kernel
#print axioms band047_checked

end ForestUnimodality.IntermediateBridgeCoverData

