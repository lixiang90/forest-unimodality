import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band000 : Band CellKey where
  qlo := (1/4)
  qhi := (9/35)
  mlo := (14583333333333333333333333333333/500000000000000000000000000000)
  mhi := (10329861111111111111111111111111/125000000000000000000000000000)
  cells := [(59,0),(99,0),(130,0)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 0

theorem band000_checked : band000.check rectangle=true := by decide +kernel
#print axioms band000_checked

def band001 : Band CellKey where
  qlo := (1/4)
  qhi := (9/35)
  mlo := (4861111111111111111111111111111/125000000000000000000000000000)
  mhi := (10329861111111111111111111111111/125000000000000000000000000000)
  cells := [(80,0),(99,0),(130,0)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 0

theorem band001_checked : band001.check rectangle=true := by decide +kernel
#print axioms band001_checked

def band002 : Band CellKey where
  qlo := (1/4)
  qhi := (9/35)
  mlo := (48611111111111111111111111111111/1000000000000000000000000000000)
  mhi := (10329861111111111111111111111111/125000000000000000000000000000)
  cells := [(99,0),(130,0)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 0

theorem band002_checked : band002.check rectangle=true := by decide +kernel
#print axioms band002_checked

def band003 : Band CellKey where
  qlo := (1/4)
  qhi := (9/35)
  mlo := (32083333333333333333333333333333/500000000000000000000000000000)
  mhi := (10329861111111111111111111111111/125000000000000000000000000000)
  cells := [(130,0)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 0

theorem band003_checked : band003.check rectangle=true := by decide +kernel
#print axioms band003_checked

def band004 : Band CellKey where
  qlo := (9/35)
  qhi := (37/140)
  mlo := (14189189189189189189189189189189/500000000000000000000000000000)
  mhi := (16081081081081081081081081081081/200000000000000000000000000000)
  cells := [(59,1),(99,1),(130,1)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 1

theorem band004_checked : band004.check rectangle=true := by decide +kernel
#print axioms band004_checked

def band005 : Band CellKey where
  qlo := (9/35)
  qhi := (37/140)
  mlo := (37837837837837837837837837837837/1000000000000000000000000000000)
  mhi := (16081081081081081081081081081081/200000000000000000000000000000)
  cells := [(80,1),(99,1),(130,1)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 1

theorem band005_checked : band005.check rectangle=true := by decide +kernel
#print axioms band005_checked

def band006 : Band CellKey where
  qlo := (9/35)
  qhi := (37/140)
  mlo := (47297297297297297297297297297297/1000000000000000000000000000000)
  mhi := (16081081081081081081081081081081/200000000000000000000000000000)
  cells := [(99,1),(130,1)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 1

theorem band006_checked : band006.check rectangle=true := by decide +kernel
#print axioms band006_checked

def band007 : Band CellKey where
  qlo := (9/35)
  qhi := (37/140)
  mlo := (3902027027027027027027027027027/62500000000000000000000000000)
  mhi := (16081081081081081081081081081081/200000000000000000000000000000)
  cells := [(130,1)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 1

theorem band007_checked : band007.check rectangle=true := by decide +kernel
#print axioms band007_checked

def band008 : Band CellKey where
  qlo := (37/140)
  qhi := (19/70)
  mlo := (3453947368421052631578947368421/125000000000000000000000000000)
  mhi := (7828947368421052631578947368421/100000000000000000000000000000)
  cells := [(59,2),(99,2),(130,2)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 2

theorem band008_checked : band008.check rectangle=true := by decide +kernel
#print axioms band008_checked

def band009 : Band CellKey where
  qlo := (37/140)
  qhi := (19/70)
  mlo := (36842105263157894736842105263157/1000000000000000000000000000000)
  mhi := (7828947368421052631578947368421/100000000000000000000000000000)
  cells := [(80,2),(99,2),(130,2)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 2

theorem band009_checked : band009.check rectangle=true := by decide +kernel
#print axioms band009_checked

def band010 : Band CellKey where
  qlo := (37/140)
  qhi := (19/70)
  mlo := (46052631578947368421052631578947/1000000000000000000000000000000)
  mhi := (7828947368421052631578947368421/100000000000000000000000000000)
  cells := [(99,2),(130,2)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 2

theorem band010_checked : band010.check rectangle=true := by decide +kernel
#print axioms band010_checked

def band011 : Band CellKey where
  qlo := (37/140)
  qhi := (19/70)
  mlo := (6078947368421052631578947368421/100000000000000000000000000000)
  mhi := (7828947368421052631578947368421/100000000000000000000000000000)
  cells := [(130,2)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 2

theorem band011_checked : band011.check rectangle=true := by decide +kernel
#print axioms band011_checked

def band012 : Band CellKey where
  qlo := (19/70)
  qhi := (39/140)
  mlo := (6730769230769230769230769230769/250000000000000000000000000000)
  mhi := (76282051282051282051282051282051/1000000000000000000000000000000)
  cells := [(59,3),(99,3),(130,3)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 3

theorem band012_checked : band012.check rectangle=true := by decide +kernel
#print axioms band012_checked

def band013 : Band CellKey where
  qlo := (19/70)
  qhi := (39/140)
  mlo := (7179487179487179487179487179487/200000000000000000000000000000)
  mhi := (76282051282051282051282051282051/1000000000000000000000000000000)
  cells := [(80,3),(99,3),(130,3)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 3

theorem band013_checked : band013.check rectangle=true := by decide +kernel
#print axioms band013_checked

def band014 : Band CellKey where
  qlo := (19/70)
  qhi := (39/140)
  mlo := (22435897435897435897435897435897/500000000000000000000000000000)
  mhi := (76282051282051282051282051282051/1000000000000000000000000000000)
  cells := [(99,3),(130,3)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 3

theorem band014_checked : band014.check rectangle=true := by decide +kernel
#print axioms band014_checked

def band015 : Band CellKey where
  qlo := (19/70)
  qhi := (39/140)
  mlo := (59230769230769230769230769230769/1000000000000000000000000000000)
  mhi := (76282051282051282051282051282051/1000000000000000000000000000000)
  cells := [(130,3)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 3

theorem band015_checked : band015.check rectangle=true := by decide +kernel
#print axioms band015_checked

end ForestUnimodality.IntermediateBridgeCoverData

