import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band080 : Band CellKey where
  qlo := (103/255)
  qhi := (7/17)
  mlo := (3642857142857142857142857142857/200000000000000000000000000000)
  mhi := (25803571428571428571428571428571/500000000000000000000000000000)
  cells := [(59,20),(99,20),(130,20)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 20

theorem band080_checked : band080.check rectangle=true := by decide +kernel
#print axioms band080_checked

def band081 : Band CellKey where
  qlo := (103/255)
  qhi := (7/17)
  mlo := (12142857142857142857142857142857/500000000000000000000000000000)
  mhi := (25803571428571428571428571428571/500000000000000000000000000000)
  cells := [(80,20),(99,20),(130,20)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 20

theorem band081_checked : band081.check rectangle=true := by decide +kernel
#print axioms band081_checked

def band082 : Band CellKey where
  qlo := (103/255)
  qhi := (7/17)
  mlo := (15178571428571428571428571428571/500000000000000000000000000000)
  mhi := (25803571428571428571428571428571/500000000000000000000000000000)
  cells := [(99,20),(130,20)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 20

theorem band082_checked : band082.check rectangle=true := by decide +kernel
#print axioms band082_checked

def band083 : Band CellKey where
  qlo := (103/255)
  qhi := (7/17)
  mlo := (10017857142857142857142857142857/250000000000000000000000000000)
  mhi := (25803571428571428571428571428571/500000000000000000000000000000)
  cells := [(130,20)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 20

theorem band083_checked : band083.check rectangle=true := by decide +kernel
#print axioms band083_checked

def band084 : Band CellKey where
  qlo := (7/17)
  qhi := (64/153)
  mlo := (2295/128)
  mhi := (13005/256)
  cells := [(59,21),(99,21),(130,21)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 21

theorem band084_checked : band084.check rectangle=true := by decide +kernel
#print axioms band084_checked

def band085 : Band CellKey where
  qlo := (7/17)
  qhi := (64/153)
  mlo := (765/32)
  mhi := (13005/256)
  cells := [(80,21),(99,21),(130,21)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 21

theorem band085_checked : band085.check rectangle=true := by decide +kernel
#print axioms band085_checked

def band086 : Band CellKey where
  qlo := (7/17)
  qhi := (64/153)
  mlo := (3825/128)
  mhi := (13005/256)
  cells := [(99,21),(130,21)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 21

theorem band086_checked : band086.check rectangle=true := by decide +kernel
#print axioms band086_checked

def band087 : Band CellKey where
  qlo := (7/17)
  qhi := (64/153)
  mlo := (5049/128)
  mhi := (13005/256)
  cells := [(130,21)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 21

theorem band087_checked : band087.check rectangle=true := by decide +kernel
#print axioms band087_checked

def band088 : Band CellKey where
  qlo := (64/153)
  qhi := (65/153)
  mlo := (8826923076923076923076923076923/500000000000000000000000000000)
  mhi := (5001923076923076923076923076923/100000000000000000000000000000)
  cells := [(59,22),(99,22),(130,22)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 22

theorem band088_checked : band088.check rectangle=true := by decide +kernel
#print axioms band088_checked

def band089 : Band CellKey where
  qlo := (64/153)
  qhi := (65/153)
  mlo := (23538461538461538461538461538461/1000000000000000000000000000000)
  mhi := (5001923076923076923076923076923/100000000000000000000000000000)
  cells := [(80,22),(99,22),(130,22)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 22

theorem band089_checked : band089.check rectangle=true := by decide +kernel
#print axioms band089_checked

def band090 : Band CellKey where
  qlo := (64/153)
  qhi := (65/153)
  mlo := (7355769230769230769230769230769/250000000000000000000000000000)
  mhi := (5001923076923076923076923076923/100000000000000000000000000000)
  cells := [(99,22),(130,22)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 22

theorem band090_checked : band090.check rectangle=true := by decide +kernel
#print axioms band090_checked

def band091 : Band CellKey where
  qlo := (64/153)
  qhi := (65/153)
  mlo := (38838461538461538461538461538461/1000000000000000000000000000000)
  mhi := (5001923076923076923076923076923/100000000000000000000000000000)
  cells := [(130,22)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 22

theorem band091_checked : band091.check rectangle=true := by decide +kernel
#print axioms band091_checked

def band092 : Band CellKey where
  qlo := (65/153)
  qhi := (22/51)
  mlo := (17386363636363636363636363636363/1000000000000000000000000000000)
  mhi := (49261363636363636363636363636363/1000000000000000000000000000000)
  cells := [(59,23),(99,23),(130,23)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 23

theorem band092_checked : band092.check rectangle=true := by decide +kernel
#print axioms band092_checked

def band093 : Band CellKey where
  qlo := (65/153)
  qhi := (22/51)
  mlo := (24340909090909090909090909090909/1000000000000000000000000000000)
  mhi := (49261363636363636363636363636363/1000000000000000000000000000000)
  cells := [(80,23),(99,23),(130,23)]
  lowerOrder := 80
  orderCap := 98
  rank := 21
  parentStrip := 23

theorem band093_checked : band093.check rectangle=true := by decide +kernel
#print axioms band093_checked

def band094 : Band CellKey where
  qlo := (65/153)
  qhi := (22/51)
  mlo := (3622159090909090909090909090909/125000000000000000000000000000)
  mhi := (49261363636363636363636363636363/1000000000000000000000000000000)
  cells := [(99,23),(130,23)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 23

theorem band094_checked : band094.check rectangle=true := by decide +kernel
#print axioms band094_checked

def band095 : Band CellKey where
  qlo := (65/153)
  qhi := (22/51)
  mlo := (153/4)
  mhi := (49261363636363636363636363636363/1000000000000000000000000000000)
  cells := [(130,23)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 23

theorem band095_checked : band095.check rectangle=true := by decide +kernel
#print axioms band095_checked

end ForestUnimodality.IntermediateBridgeCoverData

