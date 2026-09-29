import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band496 : Band CellKey where
  qlo := (2587/4752)
  qhi := (6/11)
  mlo := (33/2)
  mhi := (22406275344035344294896730234757/500000000000000000000000000000)
  cells := [(59,201),(99,158),(130,213)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 100

theorem band496_checked : band496.check rectangle=true := by decide +kernel
#print axioms band496_checked

def band497 : Band CellKey where
  qlo := (2587/4752)
  qhi := (6/11)
  mlo := (22/1)
  mhi := (22406275344035344294896730234757/500000000000000000000000000000)
  cells := [(80,191),(99,158),(130,213)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 100

theorem band497_checked : band497.check rectangle=true := by decide +kernel
#print axioms band497_checked

def band498 : Band CellKey where
  qlo := (2587/4752)
  qhi := (6/11)
  mlo := (26583333333333333333333333333333/1000000000000000000000000000000)
  mhi := (22406275344035344294896730234757/500000000000000000000000000000)
  cells := [(99,158),(130,213)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 100

theorem band498_checked : band498.check rectangle=true := by decide +kernel
#print axioms band498_checked

def band499 : Band CellKey where
  qlo := (2587/4752)
  qhi := (6/11)
  mlo := (34833333333333333333333333333333/1000000000000000000000000000000)
  mhi := (22406275344035344294896730234757/500000000000000000000000000000)
  cells := [(130,213)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 100

theorem band499_checked : band499.check rectangle=true := by decide +kernel
#print axioms band499_checked

def band500 : Band CellKey where
  qlo := (6/11)
  qhi := (97/177)
  mlo := (1642268041237113402061855670103/100000000000000000000000000000)
  mhi := (11193909378692214935203160677353/250000000000000000000000000000)
  cells := [(59,202),(99,159),(130,214)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 101

theorem band500_checked : band500.check rectangle=true := by decide +kernel
#print axioms band500_checked

def band501 : Band CellKey where
  qlo := (6/11)
  qhi := (97/177)
  mlo := (21896907216494845360824742268041/1000000000000000000000000000000)
  mhi := (11193909378692214935203160677353/250000000000000000000000000000)
  cells := [(80,192),(80,193),(80,194),(80,195),(80,196),(99,159),(130,214)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 101

theorem band501_checked : band501.check rectangle=true := by decide +kernel
#print axioms band501_checked

def band502 : Band CellKey where
  qlo := (6/11)
  qhi := (97/177)
  mlo := (1653672680412371134020618556701/62500000000000000000000000000)
  mhi := (11193909378692214935203160677353/250000000000000000000000000000)
  cells := [(99,159),(130,214)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 101

theorem band502_checked : band502.check rectangle=true := by decide +kernel
#print axioms band502_checked

def band503 : Band CellKey where
  qlo := (6/11)
  qhi := (97/177)
  mlo := (34670103092783505154639175257731/1000000000000000000000000000000)
  mhi := (11193909378692214935203160677353/250000000000000000000000000000)
  cells := [(130,214)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 101

theorem band503_checked : band503.check rectangle=true := by decide +kernel
#print axioms band503_checked

def band504 : Band CellKey where
  qlo := (97/177)
  qhi := (49/89)
  mlo := (2043367346938775510204081632653/125000000000000000000000000000)
  mhi := (22336963175717711257254854981981/500000000000000000000000000000)
  cells := [(59,203),(99,160),(130,215)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 102

theorem band504_checked : band504.check rectangle=true := by decide +kernel
#print axioms band504_checked

def band505 : Band CellKey where
  qlo := (97/177)
  qhi := (49/89)
  mlo := (681122448979591836734693877551/31250000000000000000000000000)
  mhi := (22336963175717711257254854981981/500000000000000000000000000000)
  cells := [(80,197),(99,160),(130,215)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 102

theorem band505_checked : band505.check rectangle=true := by decide +kernel
#print axioms band505_checked

def band506 : Band CellKey where
  qlo := (97/177)
  qhi := (49/89)
  mlo := (13168367346938775510204081632653/500000000000000000000000000000)
  mhi := (22336963175717711257254854981981/500000000000000000000000000000)
  cells := [(99,160),(130,215)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 102

theorem band506_checked : band506.check rectangle=true := by decide +kernel
#print axioms band506_checked

def band507 : Band CellKey where
  qlo := (97/177)
  qhi := (49/89)
  mlo := (17255102040816326530612244897959/500000000000000000000000000000)
  mhi := (22336963175717711257254854981981/500000000000000000000000000000)
  cells := [(130,215)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 102

theorem band507_checked : band507.check rectangle=true := by decide +kernel
#print axioms band507_checked

def band508 : Band CellKey where
  qlo := (49/89)
  qhi := (99/179)
  mlo := (16272727272727272727272727272727/1000000000000000000000000000000)
  mhi := (44574023367640427775286898123707/1000000000000000000000000000000)
  cells := [(59,204),(99,161),(130,216)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 103

theorem band508_checked : band508.check rectangle=true := by decide +kernel
#print axioms band508_checked

def band509 : Band CellKey where
  qlo := (49/89)
  qhi := (99/179)
  mlo := (21696969696969696969696969696969/1000000000000000000000000000000)
  mhi := (44574023367640427775286898123707/1000000000000000000000000000000)
  cells := [(80,198),(99,161),(130,216)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 103

theorem band509_checked : band509.check rectangle=true := by decide +kernel
#print axioms band509_checked

def band510 : Band CellKey where
  qlo := (49/89)
  qhi := (99/179)
  mlo := (26217171717171717171717171717171/1000000000000000000000000000000)
  mhi := (44574023367640427775286898123707/1000000000000000000000000000000)
  cells := [(99,161),(130,216)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 103

theorem band510_checked : band510.check rectangle=true := by decide +kernel
#print axioms band510_checked

def band511 : Band CellKey where
  qlo := (49/89)
  qhi := (99/179)
  mlo := (6870707070707070707070707070707/200000000000000000000000000000)
  mhi := (44574023367640427775286898123707/1000000000000000000000000000000)
  cells := [(130,216)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 103

theorem band511_checked : band511.check rectangle=true := by decide +kernel
#print axioms band511_checked

end ForestUnimodality.IntermediateBridgeCoverData

