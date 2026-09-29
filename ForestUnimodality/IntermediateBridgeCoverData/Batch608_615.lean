import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band608 : Band CellKey where
  qlo := (53/78)
  qhi := (107/156)
  mlo := (2915887850467289719626168224299/200000000000000000000000000000)
  mhi := (39929366271594058198007416324801/1000000000000000000000000000000)
  cells := [(59,229),(99,186),(130,241)]
  lowerOrder := 59
  orderCap := 79
  rank := 20
  parentStrip := 128

theorem band608_checked : band608.check rectangle=true := by decide +kernel
#print axioms band608_checked

def band609 : Band CellKey where
  qlo := (53/78)
  qhi := (107/156)
  mlo := (9841121495327102803738317757009/500000000000000000000000000000)
  mhi := (39929366271594058198007416324801/1000000000000000000000000000000)
  cells := [(80,234),(99,186),(130,241)]
  lowerOrder := 80
  orderCap := 98
  rank := 27
  parentStrip := 128

theorem band609_checked : band609.check rectangle=true := by decide +kernel
#print axioms band609_checked

def band610 : Band CellKey where
  qlo := (53/78)
  qhi := (107/156)
  mlo := (24056074766355140186915887850467/1000000000000000000000000000000)
  mhi := (39929366271594058198007416324801/1000000000000000000000000000000)
  cells := [(99,186),(130,241)]
  lowerOrder := 99
  orderCap := 129
  rank := 33
  parentStrip := 128

theorem band610_checked : band610.check rectangle=true := by decide +kernel
#print axioms band610_checked

def band611 : Band CellKey where
  qlo := (53/78)
  qhi := (107/156)
  mlo := (1530841121495327102803738317757/50000000000000000000000000000)
  mhi := (39929366271594058198007416324801/1000000000000000000000000000000)
  cells := [(130,241)]
  lowerOrder := 130
  orderCap := 169
  rank := 42
  parentStrip := 128

theorem band611_checked : band611.check rectangle=true := by decide +kernel
#print axioms band611_checked

def band612 : Band CellKey where
  qlo := (107/156)
  qhi := (9/13)
  mlo := (3611111111111111111111111111111/250000000000000000000000000000)
  mhi := (39745814003913943733092751650657/1000000000000000000000000000000)
  cells := [(59,230),(99,187),(130,242)]
  lowerOrder := 59
  orderCap := 79
  rank := 20
  parentStrip := 129

theorem band612_checked : band612.check rectangle=true := by decide +kernel
#print axioms band612_checked

def band613 : Band CellKey where
  qlo := (107/156)
  qhi := (9/13)
  mlo := (39/2)
  mhi := (39745814003913943733092751650657/1000000000000000000000000000000)
  cells := [(80,235),(99,187),(130,242)]
  lowerOrder := 80
  orderCap := 98
  rank := 27
  parentStrip := 129

theorem band613_checked : band613.check rectangle=true := by decide +kernel
#print axioms band613_checked

def band614 : Band CellKey where
  qlo := (107/156)
  qhi := (9/13)
  mlo := (23833333333333333333333333333333/1000000000000000000000000000000)
  mhi := (39745814003913943733092751650657/1000000000000000000000000000000)
  cells := [(99,187),(130,242)]
  lowerOrder := 99
  orderCap := 129
  rank := 33
  parentStrip := 129

theorem band614_checked : band614.check rectangle=true := by decide +kernel
#print axioms band614_checked

def band615 : Band CellKey where
  qlo := (107/156)
  qhi := (9/13)
  mlo := (6211111111111111111111111111111/200000000000000000000000000000)
  mhi := (39745814003913943733092751650657/1000000000000000000000000000000)
  cells := [(130,242)]
  lowerOrder := 130
  orderCap := 169
  rank := 43
  parentStrip := 129

theorem band615_checked : band615.check rectangle=true := by decide +kernel
#print axioms band615_checked

end ForestUnimodality.IntermediateBridgeCoverData

