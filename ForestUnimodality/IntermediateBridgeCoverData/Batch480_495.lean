import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band480 : Band CellKey where
  qlo := (2567/4752)
  qhi := (643/1188)
  mlo := (16628304821150855365474339035769/1000000000000000000000000000000)
  mhi := (44985085483857897875987910014081/1000000000000000000000000000000)
  cells := [(59,197),(99,157),(130,212)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 99

theorem band480_checked : band480.check rectangle=true := by decide +kernel
#print axioms band480_checked

def band481 : Band CellKey where
  qlo := (2567/4752)
  qhi := (643/1188)
  mlo := (11085536547433903576982892690513/500000000000000000000000000000)
  mhi := (44985085483857897875987910014081/1000000000000000000000000000000)
  cells := [(80,187),(99,157),(130,212)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 99

theorem band481_checked : band481.check rectangle=true := by decide +kernel
#print axioms band481_checked

def band482 : Band CellKey where
  qlo := (2567/4752)
  qhi := (643/1188)
  mlo := (1339502332814930015552099533437/50000000000000000000000000000)
  mhi := (44985085483857897875987910014081/1000000000000000000000000000000)
  cells := [(99,157),(130,212)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 99

theorem band482_checked : band482.check rectangle=true := by decide +kernel
#print axioms band482_checked

def band483 : Band CellKey where
  qlo := (2567/4752)
  qhi := (643/1188)
  mlo := (280833592534992223950233281493/8000000000000000000000000000)
  mhi := (44985085483857897875987910014081/1000000000000000000000000000000)
  cells := [(130,212)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 99

theorem band483_checked : band483.check rectangle=true := by decide +kernel
#print axioms band483_checked

def band484 : Band CellKey where
  qlo := (643/1188)
  qhi := (859/1584)
  mlo := (414901047729918509895227008149/25000000000000000000000000000)
  mhi := (22406275344035344294896730234757/500000000000000000000000000000)
  cells := [(59,198),(99,158),(130,213)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 100

theorem band484_checked : band484.check rectangle=true := by decide +kernel
#print axioms band484_checked

def band485 : Band CellKey where
  qlo := (643/1188)
  qhi := (859/1584)
  mlo := (138300349243306169965075669383/6250000000000000000000000000)
  mhi := (22406275344035344294896730234757/500000000000000000000000000000)
  cells := [(80,188),(99,158),(130,213)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 100

theorem band485_checked : band485.check rectangle=true := by decide +kernel
#print axioms band485_checked

def band486 : Band CellKey where
  qlo := (643/1188)
  qhi := (859/1584)
  mlo := (26583333333333333333333333333333/1000000000000000000000000000000)
  mhi := (22406275344035344294896730234757/500000000000000000000000000000)
  cells := [(99,158),(130,213)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 100

theorem band486_checked : band486.check rectangle=true := by decide +kernel
#print axioms band486_checked

def band487 : Band CellKey where
  qlo := (643/1188)
  qhi := (859/1584)
  mlo := (34833333333333333333333333333333/1000000000000000000000000000000)
  mhi := (22406275344035344294896730234757/500000000000000000000000000000)
  cells := [(130,213)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 100

theorem band487_checked : band487.check rectangle=true := by decide +kernel
#print axioms band487_checked

def band488 : Band CellKey where
  qlo := (859/1584)
  qhi := (1291/2376)
  mlo := (16563903950426026336173508907823/1000000000000000000000000000000)
  mhi := (22406275344035344294896730234757/500000000000000000000000000000)
  cells := [(59,199),(99,158),(130,213)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 100

theorem band488_checked : band488.check rectangle=true := by decide +kernel
#print axioms band488_checked

def band489 : Band CellKey where
  qlo := (859/1584)
  qhi := (1291/2376)
  mlo := (5521301316808675445391169635941/250000000000000000000000000000)
  mhi := (22406275344035344294896730234757/500000000000000000000000000000)
  cells := [(80,189),(99,158),(130,213)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 100

theorem band489_checked : band489.check rectangle=true := by decide +kernel
#print axioms band489_checked

def band490 : Band CellKey where
  qlo := (859/1584)
  qhi := (1291/2376)
  mlo := (26583333333333333333333333333333/1000000000000000000000000000000)
  mhi := (22406275344035344294896730234757/500000000000000000000000000000)
  cells := [(99,158),(130,213)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 100

theorem band490_checked : band490.check rectangle=true := by decide +kernel
#print axioms band490_checked

def band491 : Band CellKey where
  qlo := (859/1584)
  qhi := (1291/2376)
  mlo := (34833333333333333333333333333333/1000000000000000000000000000000)
  mhi := (22406275344035344294896730234757/500000000000000000000000000000)
  cells := [(130,213)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 100

theorem band491_checked : band491.check rectangle=true := by decide +kernel
#print axioms band491_checked

def band492 : Band CellKey where
  qlo := (1291/2376)
  qhi := (2587/4752)
  mlo := (16531890220332431387707769617317/1000000000000000000000000000000)
  mhi := (22406275344035344294896730234757/500000000000000000000000000000)
  cells := [(59,200),(99,158),(130,213)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 100

theorem band492_checked : band492.check rectangle=true := by decide +kernel
#print axioms band492_checked

def band493 : Band CellKey where
  qlo := (1291/2376)
  qhi := (2587/4752)
  mlo := (5510630073444143795902589872439/250000000000000000000000000000)
  mhi := (22406275344035344294896730234757/500000000000000000000000000000)
  cells := [(80,190),(99,158),(130,213)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 100

theorem band493_checked : band493.check rectangle=true := by decide +kernel
#print axioms band493_checked

def band494 : Band CellKey where
  qlo := (1291/2376)
  qhi := (2587/4752)
  mlo := (26583333333333333333333333333333/1000000000000000000000000000000)
  mhi := (22406275344035344294896730234757/500000000000000000000000000000)
  cells := [(99,158),(130,213)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 100

theorem band494_checked : band494.check rectangle=true := by decide +kernel
#print axioms band494_checked

def band495 : Band CellKey where
  qlo := (1291/2376)
  qhi := (2587/4752)
  mlo := (34833333333333333333333333333333/1000000000000000000000000000000)
  mhi := (22406275344035344294896730234757/500000000000000000000000000000)
  cells := [(130,213)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 100

theorem band495_checked : band495.check rectangle=true := by decide +kernel
#print axioms band495_checked

end ForestUnimodality.IntermediateBridgeCoverData

