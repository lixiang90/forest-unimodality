import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band592 : Band CellKey where
  qlo := (41/63)
  qhi := (83/126)
  mlo := (288433734939759036144578313253/20000000000000000000000000000)
  mhi := (40688817608243152393193031535457/1000000000000000000000000000000)
  cells := [(59,225),(99,182),(130,237)]
  lowerOrder := 59
  orderCap := 79
  rank := 19
  parentStrip := 124

theorem band592_checked : band592.check rectangle=true := by decide +kernel
#print axioms band592_checked

def band593 : Band CellKey where
  qlo := (41/63)
  qhi := (83/126)
  mlo := (1233433734939759036144578313253/62500000000000000000000000000)
  mhi := (40688817608243152393193031535457/1000000000000000000000000000000)
  cells := [(80,228),(99,182),(130,237)]
  lowerOrder := 80
  orderCap := 98
  rank := 26
  parentStrip := 124

theorem band593_checked : band593.check rectangle=true := by decide +kernel
#print axioms band593_checked

def band594 : Band CellKey where
  qlo := (41/63)
  qhi := (83/126)
  mlo := (12144578313253012048192771084337/500000000000000000000000000000)
  mhi := (40688817608243152393193031535457/1000000000000000000000000000000)
  cells := [(99,182),(130,237)]
  lowerOrder := 99
  orderCap := 129
  rank := 32
  parentStrip := 124

theorem band594_checked : band594.check rectangle=true := by decide +kernel
#print axioms band594_checked

def band595 : Band CellKey where
  qlo := (41/63)
  qhi := (83/126)
  mlo := (15560240963855421686746987951807/500000000000000000000000000000)
  mhi := (40688817608243152393193031535457/1000000000000000000000000000000)
  cells := [(130,237)]
  lowerOrder := 130
  orderCap := 169
  rank := 41
  parentStrip := 124

theorem band595_checked : band595.check rectangle=true := by decide +kernel
#print axioms band595_checked

def band596 : Band CellKey where
  qlo := (83/126)
  qhi := (2/3)
  mlo := (15/1)
  mhi := (8089766596933620079738246088499/200000000000000000000000000000)
  cells := [(59,226),(99,183),(130,238)]
  lowerOrder := 59
  orderCap := 79
  rank := 20
  parentStrip := 125

theorem band596_checked : band596.check rectangle=true := by decide +kernel
#print axioms band596_checked

def band597 : Band CellKey where
  qlo := (83/126)
  qhi := (2/3)
  mlo := (39/2)
  mhi := (8089766596933620079738246088499/200000000000000000000000000000)
  cells := [(80,229),(99,183),(130,238)]
  lowerOrder := 80
  orderCap := 98
  rank := 26
  parentStrip := 125

theorem band597_checked : band597.check rectangle=true := by decide +kernel
#print axioms band597_checked

def band598 : Band CellKey where
  qlo := (83/126)
  qhi := (2/3)
  mlo := (24/1)
  mhi := (8089766596933620079738246088499/200000000000000000000000000000)
  cells := [(99,183),(130,238)]
  lowerOrder := 99
  orderCap := 129
  rank := 32
  parentStrip := 125

theorem band598_checked : band598.check rectangle=true := by decide +kernel
#print axioms band598_checked

def band599 : Band CellKey where
  qlo := (83/126)
  qhi := (2/3)
  mlo := (63/2)
  mhi := (8089766596933620079738246088499/200000000000000000000000000000)
  cells := [(130,238)]
  lowerOrder := 130
  orderCap := 169
  rank := 42
  parentStrip := 125

theorem band599_checked : band599.check rectangle=true := by decide +kernel
#print axioms band599_checked

def band600 : Band CellKey where
  qlo := (2/3)
  qhi := (35/52)
  mlo := (7428571428571428571428571428571/500000000000000000000000000000)
  mhi := (5038028803202905671217850302067/125000000000000000000000000000)
  cells := [(59,227),(99,184),(130,239)]
  lowerOrder := 59
  orderCap := 79
  rank := 20
  parentStrip := 126

theorem band600_checked : band600.check rectangle=true := by decide +kernel
#print axioms band600_checked

def band601 : Band CellKey where
  qlo := (2/3)
  qhi := (35/52)
  mlo := (3862857142857142857142857142857/200000000000000000000000000000)
  mhi := (5038028803202905671217850302067/125000000000000000000000000000)
  cells := [(80,230),(80,231),(80,232),(99,184),(130,239)]
  lowerOrder := 80
  orderCap := 98
  rank := 26
  parentStrip := 126

theorem band601_checked : band601.check rectangle=true := by decide +kernel
#print axioms band601_checked

def band602 : Band CellKey where
  qlo := (2/3)
  qhi := (35/52)
  mlo := (5942857142857142857142857142857/250000000000000000000000000000)
  mhi := (5038028803202905671217850302067/125000000000000000000000000000)
  cells := [(99,184),(130,239)]
  lowerOrder := 99
  orderCap := 129
  rank := 32
  parentStrip := 126

theorem band602_checked : band602.check rectangle=true := by decide +kernel
#print axioms band602_checked

def band603 : Band CellKey where
  qlo := (2/3)
  qhi := (35/52)
  mlo := (156/5)
  mhi := (5038028803202905671217850302067/125000000000000000000000000000)
  cells := [(130,239)]
  lowerOrder := 130
  orderCap := 169
  rank := 42
  parentStrip := 126

theorem band603_checked : band603.check rectangle=true := by decide +kernel
#print axioms band603_checked

def band604 : Band CellKey where
  qlo := (35/52)
  qhi := (53/78)
  mlo := (14716981132075471698113207547169/1000000000000000000000000000000)
  mhi := (40115484958451957419096200900857/1000000000000000000000000000000)
  cells := [(59,228),(99,185),(130,240)]
  lowerOrder := 59
  orderCap := 79
  rank := 20
  parentStrip := 127

theorem band604_checked : band604.check rectangle=true := by decide +kernel
#print axioms band604_checked

def band605 : Band CellKey where
  qlo := (35/52)
  qhi := (53/78)
  mlo := (19867924528301886792452830188679/1000000000000000000000000000000)
  mhi := (40115484958451957419096200900857/1000000000000000000000000000000)
  cells := [(80,233),(99,185),(130,240)]
  lowerOrder := 80
  orderCap := 98
  rank := 27
  parentStrip := 127

theorem band605_checked : band605.check rectangle=true := by decide +kernel
#print axioms band605_checked

def band606 : Band CellKey where
  qlo := (35/52)
  qhi := (53/78)
  mlo := (23547169811320754716981132075471/1000000000000000000000000000000)
  mhi := (40115484958451957419096200900857/1000000000000000000000000000000)
  cells := [(99,185),(130,240)]
  lowerOrder := 99
  orderCap := 129
  rank := 32
  parentStrip := 127

theorem band606_checked : band606.check rectangle=true := by decide +kernel
#print axioms band606_checked

def band607 : Band CellKey where
  qlo := (35/52)
  qhi := (53/78)
  mlo := (965801886792452830188679245283/31250000000000000000000000000)
  mhi := (40115484958451957419096200900857/1000000000000000000000000000000)
  cells := [(130,240)]
  lowerOrder := 130
  orderCap := 169
  rank := 42
  parentStrip := 127

theorem band607_checked : band607.check rectangle=true := by decide +kernel
#print axioms band607_checked

end ForestUnimodality.IntermediateBridgeCoverData

