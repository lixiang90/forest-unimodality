import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band128 : Band CellKey where
  qlo := (841/1786)
  qhi := (1687/3572)
  mlo := (1058684054534676941315945465323/62500000000000000000000000000)
  mhi := (44994072317723770005927682276229/1000000000000000000000000000000)
  cells := [(59,35),(59,36),(99,32),(130,32)]
  lowerOrder := 59
  orderCap := 79
  rank := 16
  parentStrip := 32

theorem band128_checked : band128.check rectangle=true := by decide +kernel
#print axioms band128_checked

def band129 : Band CellKey where
  qlo := (841/1786)
  qhi := (1687/3572)
  mlo := (23291049199762892708950800237107/1000000000000000000000000000000)
  mhi := (44994072317723770005927682276229/1000000000000000000000000000000)
  cells := [(80,32),(80,33),(80,34),(99,32),(130,32)]
  lowerOrder := 80
  orderCap := 98
  rank := 22
  parentStrip := 32

theorem band129_checked : band129.check rectangle=true := by decide +kernel
#print axioms band129_checked

def band130 : Band CellKey where
  qlo := (841/1786)
  qhi := (1687/3572)
  mlo := (27525785417901600474214582098399/1000000000000000000000000000000)
  mhi := (44994072317723770005927682276229/1000000000000000000000000000000)
  cells := [(99,32),(130,32)]
  lowerOrder := 99
  orderCap := 129
  rank := 26
  parentStrip := 32

theorem band130_checked : band130.check rectangle=true := by decide +kernel
#print axioms band130_checked

def band131 : Band CellKey where
  qlo := (841/1786)
  qhi := (1687/3572)
  mlo := (1746828689982216953171310017783/50000000000000000000000000000)
  mhi := (44994072317723770005927682276229/1000000000000000000000000000000)
  cells := [(130,32)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 32

theorem band131_checked : band131.check rectangle=true := by decide +kernel
#print axioms band131_checked

def band132 : Band CellKey where
  qlo := (1687/3572)
  qhi := (9/19)
  mlo := (2111111111111111111111111111111/125000000000000000000000000000)
  mhi := (44861111111111111111111111111111/1000000000000000000000000000000)
  cells := [(59,37),(59,38),(99,33),(130,33)]
  lowerOrder := 59
  orderCap := 79
  rank := 16
  parentStrip := 33

theorem band132_checked : band132.check rectangle=true := by decide +kernel
#print axioms band132_checked

def band133 : Band CellKey where
  qlo := (1687/3572)
  qhi := (9/19)
  mlo := (11611111111111111111111111111111/500000000000000000000000000000)
  mhi := (44861111111111111111111111111111/1000000000000000000000000000000)
  cells := [(80,35),(80,36),(80,37),(99,33),(130,33)]
  lowerOrder := 80
  orderCap := 98
  rank := 22
  parentStrip := 33

theorem band133_checked : band133.check rectangle=true := by decide +kernel
#print axioms band133_checked

def band134 : Band CellKey where
  qlo := (1687/3572)
  qhi := (9/19)
  mlo := (6861111111111111111111111111111/250000000000000000000000000000)
  mhi := (44861111111111111111111111111111/1000000000000000000000000000000)
  cells := [(99,33),(130,33)]
  lowerOrder := 99
  orderCap := 129
  rank := 26
  parentStrip := 33

theorem band134_checked : band134.check rectangle=true := by decide +kernel
#print axioms band134_checked

def band135 : Band CellKey where
  qlo := (1687/3572)
  qhi := (9/19)
  mlo := (34833333333333333333333333333333/1000000000000000000000000000000)
  mhi := (44861111111111111111111111111111/1000000000000000000000000000000)
  cells := [(130,33)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 33

theorem band135_checked : band135.check rectangle=true := by decide +kernel
#print axioms band135_checked

def band136 : Band CellKey where
  qlo := (9/19)
  qhi := (1733/3648)
  mlo := (16840161569532602423542989036353/1000000000000000000000000000000)
  mhi := (44731679169070975187536064627813/1000000000000000000000000000000)
  cells := [(59,39),(59,40),(99,34),(99,35),(130,34)]
  lowerOrder := 59
  orderCap := 79
  rank := 16
  parentStrip := 34

theorem band136_checked : band136.check rectangle=true := by decide +kernel
#print axioms band136_checked

def band137 : Band CellKey where
  qlo := (9/19)
  qhi := (1733/3648)
  mlo := (4631044431621465666474321984997/200000000000000000000000000000)
  mhi := (44731679169070975187536064627813/1000000000000000000000000000000)
  cells := [(80,38),(99,34),(99,35),(130,34)]
  lowerOrder := 80
  orderCap := 98
  rank := 22
  parentStrip := 34

theorem band137_checked : band137.check rectangle=true := by decide +kernel
#print axioms band137_checked

def band138 : Band CellKey where
  qlo := (9/19)
  qhi := (1733/3648)
  mlo := (27365262550490478938257357184073/1000000000000000000000000000000)
  mhi := (44731679169070975187536064627813/1000000000000000000000000000000)
  cells := [(99,34),(99,35),(130,34)]
  lowerOrder := 99
  orderCap := 129
  rank := 26
  parentStrip := 34

theorem band138_checked : band138.check rectangle=true := by decide +kernel
#print axioms band138_checked

def band139 : Band CellKey where
  qlo := (9/19)
  qhi := (1733/3648)
  mlo := (17366416618580496249278707443739/500000000000000000000000000000)
  mhi := (44731679169070975187536064627813/1000000000000000000000000000000)
  cells := [(130,34)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 34

theorem band139_checked : band139.check rectangle=true := by decide +kernel
#print axioms band139_checked

def band140 : Band CellKey where
  qlo := (1733/3648)
  qhi := (869/1824)
  mlo := (16791714614499424626006904487917/1000000000000000000000000000000)
  mhi := (44602991944764096662830840046029/1000000000000000000000000000000)
  cells := [(59,41),(59,42),(99,36),(99,37),(130,35)]
  lowerOrder := 59
  orderCap := 79
  rank := 16
  parentStrip := 35

theorem band140_checked : band140.check rectangle=true := by decide +kernel
#print axioms band140_checked

def band141 : Band CellKey where
  qlo := (1733/3648)
  qhi := (869/1824)
  mlo := (11544303797468354430379746835443/500000000000000000000000000000)
  mhi := (44602991944764096662830840046029/1000000000000000000000000000000)
  cells := [(80,39),(99,36),(99,37),(130,35)]
  lowerOrder := 80
  orderCap := 98
  rank := 22
  parentStrip := 35

theorem band141_checked : band141.check rectangle=true := by decide +kernel
#print axioms band141_checked

def band142 : Band CellKey where
  qlo := (1733/3648)
  qhi := (869/1824)
  mlo := (5457307249712313003452243958573/200000000000000000000000000000)
  mhi := (44602991944764096662830840046029/1000000000000000000000000000000)
  cells := [(99,36),(99,37),(130,35)]
  lowerOrder := 99
  orderCap := 129
  rank := 26
  parentStrip := 35

theorem band142_checked : band142.check rectangle=true := by decide +kernel
#print axioms band142_checked

def band143 : Band CellKey where
  qlo := (1733/3648)
  qhi := (869/1824)
  mlo := (34632911392405063291139240506329/1000000000000000000000000000000)
  mhi := (44602991944764096662830840046029/1000000000000000000000000000000)
  cells := [(130,35)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 35

theorem band143_checked : band143.check rectangle=true := by decide +kernel
#print axioms band143_checked

end ForestUnimodality.IntermediateBridgeCoverData

