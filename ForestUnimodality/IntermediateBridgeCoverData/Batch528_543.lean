import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band528 : Band CellKey where
  qlo := (21/37)
  qhi := (53/93)
  mlo := (3948113207547169811320754716981/250000000000000000000000000000)
  mhi := (43921466016328410085402741218299/1000000000000000000000000000000)
  cells := [(59,209),(99,166),(130,221)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 108

theorem band528_checked : band528.check rectangle=true := by decide +kernel
#print axioms band528_checked

def band529 : Band CellKey where
  qlo := (21/37)
  qhi := (53/93)
  mlo := (10528301886792452830188679245283/500000000000000000000000000000)
  mhi := (43921466016328410085402741218299/1000000000000000000000000000000)
  cells := [(80,207),(80,208),(80,209),(99,166),(130,221)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 108

theorem band529_checked : band529.check rectangle=true := by decide +kernel
#print axioms band529_checked

def band530 : Band CellKey where
  qlo := (21/37)
  qhi := (53/93)
  mlo := (26320754716981132075471698113207/1000000000000000000000000000000)
  mhi := (43921466016328410085402741218299/1000000000000000000000000000000)
  cells := [(99,166),(130,221)]
  lowerOrder := 99
  orderCap := 129
  rank := 30
  parentStrip := 108

theorem band530_checked : band530.check rectangle=true := by decide +kernel
#print axioms band530_checked

def band531 : Band CellKey where
  qlo := (21/37)
  qhi := (53/93)
  mlo := (34216981132075471698113207547169/1000000000000000000000000000000)
  mhi := (43921466016328410085402741218299/1000000000000000000000000000000)
  cells := [(130,221)]
  lowerOrder := 130
  orderCap := 169
  rank := 39
  parentStrip := 108

theorem band531_checked : band531.check rectangle=true := by decide +kernel
#print axioms band531_checked

def band532 : Band CellKey where
  qlo := (53/93)
  qhi := (107/187)
  mlo := (7864485981308411214953271028037/500000000000000000000000000000)
  mhi := (10958604702157012642470434874673/250000000000000000000000000000)
  cells := [(59,210),(99,167),(130,222)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 109

theorem band532_checked : band532.check rectangle=true := by decide +kernel
#print axioms band532_checked

def band533 : Band CellKey where
  qlo := (53/93)
  qhi := (107/187)
  mlo := (10485981308411214953271028037383/500000000000000000000000000000)
  mhi := (10958604702157012642470434874673/250000000000000000000000000000)
  cells := [(80,210),(80,211),(80,212),(80,213),(99,167),(130,222)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 109

theorem band533_checked : band533.check rectangle=true := by decide +kernel
#print axioms band533_checked

def band534 : Band CellKey where
  qlo := (53/93)
  qhi := (107/187)
  mlo := (26214953271028037383177570093457/1000000000000000000000000000000)
  mhi := (10958604702157012642470434874673/250000000000000000000000000000)
  cells := [(99,167),(130,222)]
  lowerOrder := 99
  orderCap := 129
  rank := 30
  parentStrip := 109

theorem band534_checked : band534.check rectangle=true := by decide +kernel
#print axioms band534_checked

def band535 : Band CellKey where
  qlo := (53/93)
  qhi := (107/187)
  mlo := (6815887850467289719626168224299/200000000000000000000000000000)
  mhi := (10958604702157012642470434874673/250000000000000000000000000000)
  cells := [(130,222)]
  lowerOrder := 130
  orderCap := 169
  rank := 39
  parentStrip := 109

theorem band535_checked : band535.check rectangle=true := by decide +kernel
#print axioms band535_checked

def band536 : Band CellKey where
  qlo := (107/187)
  qhi := (27/47)
  mlo := (7833333333333333333333333333333/500000000000000000000000000000)
  mhi := (43748799754975309099989406113401/1000000000000000000000000000000)
  cells := [(59,211),(99,168),(130,223)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 110

theorem band536_checked : band536.check rectangle=true := by decide +kernel
#print axioms band536_checked

def band537 : Band CellKey where
  qlo := (107/187)
  qhi := (27/47)
  mlo := (21759259259259259259259259259259/1000000000000000000000000000000)
  mhi := (43748799754975309099989406113401/1000000000000000000000000000000)
  cells := [(80,214),(99,168),(130,223)]
  lowerOrder := 80
  orderCap := 98
  rank := 25
  parentStrip := 110

theorem band537_checked : band537.check rectangle=true := by decide +kernel
#print axioms band537_checked

def band538 : Band CellKey where
  qlo := (107/187)
  qhi := (27/47)
  mlo := (26111111111111111111111111111111/1000000000000000000000000000000)
  mhi := (43748799754975309099989406113401/1000000000000000000000000000000)
  cells := [(99,168),(130,223)]
  lowerOrder := 99
  orderCap := 129
  rank := 30
  parentStrip := 110

theorem band538_checked : band538.check rectangle=true := by decide +kernel
#print axioms band538_checked

def band539 : Band CellKey where
  qlo := (107/187)
  qhi := (27/47)
  mlo := (8486111111111111111111111111111/250000000000000000000000000000)
  mhi := (43748799754975309099989406113401/1000000000000000000000000000000)
  cells := [(130,223)]
  lowerOrder := 130
  orderCap := 169
  rank := 39
  parentStrip := 110

theorem band539_checked : band539.check rectangle=true := by decide +kernel
#print axioms band539_checked

def band540 : Band CellKey where
  qlo := (27/47)
  qhi := (653/1128)
  mlo := (3109341500765696784073506891271/200000000000000000000000000000)
  mhi := (43500057880267959655759105762863/1000000000000000000000000000000)
  cells := [(59,212),(99,169),(130,224)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 111

theorem band540_checked : band540.check rectangle=true := by decide +kernel
#print axioms band540_checked

def band541 : Band CellKey where
  qlo := (27/47)
  qhi := (653/1128)
  mlo := (21592649310872894333843797856049/1000000000000000000000000000000)
  mhi := (43500057880267959655759105762863/1000000000000000000000000000000)
  cells := [(80,215),(99,169),(130,224)]
  lowerOrder := 80
  orderCap := 98
  rank := 25
  parentStrip := 111

theorem band541_checked : band541.check rectangle=true := by decide +kernel
#print axioms band541_checked

def band542 : Band CellKey where
  qlo := (27/47)
  qhi := (653/1128)
  mlo := (12955589586523736600306278713629/500000000000000000000000000000)
  mhi := (43500057880267959655759105762863/1000000000000000000000000000000)
  cells := [(99,169),(130,224)]
  lowerOrder := 99
  orderCap := 129
  rank := 30
  parentStrip := 111

theorem band542_checked : band542.check rectangle=true := by decide +kernel
#print axioms band542_checked

def band543 : Band CellKey where
  qlo := (27/47)
  qhi := (653/1128)
  mlo := (8421133231240428790199081163859/250000000000000000000000000000)
  mhi := (43500057880267959655759105762863/1000000000000000000000000000000)
  cells := [(130,224)]
  lowerOrder := 130
  orderCap := 169
  rank := 39
  parentStrip := 111

theorem band543_checked : band543.check rectangle=true := by decide +kernel
#print axioms band543_checked

end ForestUnimodality.IntermediateBridgeCoverData

