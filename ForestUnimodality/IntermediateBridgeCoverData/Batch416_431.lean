import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band416 : Band CellKey where
  qlo := (95699/180624)
  qhi := (7977/15052)
  mlo := (3396464836404663407295975930801/200000000000000000000000000000)
  mhi := (182461523871945710490940864121/4000000000000000000000000000)
  cells := [(59,181),(99,144),(130,181),(130,182),(130,183)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 92

theorem band416_checked : band416.check rectangle=true := by decide +kernel
#print axioms band416_checked

def band417 : Band CellKey where
  qlo := (95699/180624)
  qhi := (7977/15052)
  mlo := (1132154945468221135765325310267/50000000000000000000000000000)
  mhi := (182461523871945710490940864121/4000000000000000000000000000)
  cells := [(80,161),(99,144),(130,181),(130,182),(130,183)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 92

theorem band417_checked : band417.check rectangle=true := by decide +kernel
#print axioms band417_checked

def band418 : Band CellKey where
  qlo := (95699/180624)
  qhi := (7977/15052)
  mlo := (6840102795537169361915507082863/250000000000000000000000000000)
  mhi := (182461523871945710490940864121/4000000000000000000000000000)
  cells := [(99,144),(130,181),(130,182),(130,183)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 92

theorem band418_checked : band418.check rectangle=true := by decide +kernel
#print axioms band418_checked

def band419 : Band CellKey where
  qlo := (95699/180624)
  qhi := (7977/15052)
  mlo := (34908110818603485019430863733233/1000000000000000000000000000000)
  mhi := (182461523871945710490940864121/4000000000000000000000000000)
  cells := [(130,181),(130,182),(130,183)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 92

theorem band419_checked : band419.check rectangle=true := by decide +kernel
#print axioms band419_checked

def band420 : Band CellKey where
  qlo := (7977/15052)
  qhi := (95749/180624)
  mlo := (8488945054256441320535984710023/500000000000000000000000000000)
  mhi := (22795798992806833441424721119097/500000000000000000000000000000)
  cells := [(59,182),(99,145),(130,184),(130,185),(130,186)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 93

theorem band420_checked : band420.check rectangle=true := by decide +kernel
#print axioms band420_checked

def band421 : Band CellKey where
  qlo := (7977/15052)
  qhi := (95749/180624)
  mlo := (2829648351418813773511994903341/125000000000000000000000000000)
  mhi := (22795798992806833441424721119097/500000000000000000000000000000)
  cells := [(80,162),(99,145),(130,184),(130,185),(130,186)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 93

theorem band421_checked : band421.check rectangle=true := by decide +kernel
#print axioms band421_checked

def band422 : Band CellKey where
  qlo := (7977/15052)
  qhi := (95749/180624)
  mlo := (27353267397048533143949284065629/1000000000000000000000000000000)
  mhi := (22795798992806833441424721119097/500000000000000000000000000000)
  cells := [(99,145),(130,184),(130,185),(130,186)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 93

theorem band422_checked : band422.check rectangle=true := by decide +kernel
#print axioms band422_checked

def band423 : Band CellKey where
  qlo := (7977/15052)
  qhi := (95749/180624)
  mlo := (272648408860666952135270342249/7812500000000000000000000000)
  mhi := (22795798992806833441424721119097/500000000000000000000000000000)
  cells := [(130,184),(130,185),(130,186)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 93

theorem band423_checked : band423.check rectangle=true := by decide +kernel
#print axioms band423_checked

def band424 : Band CellKey where
  qlo := (95749/180624)
  qhi := (47887/90312)
  mlo := (16973458349865307912377054315367/1000000000000000000000000000000)
  mhi := (22795798992806833441424721119097/500000000000000000000000000000)
  cells := [(59,183),(99,146),(130,187),(130,188),(130,189)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 93

theorem band424_checked : band424.check rectangle=true := by decide +kernel
#print axioms band424_checked

def band425 : Band CellKey where
  qlo := (95749/180624)
  qhi := (47887/90312)
  mlo := (22631277799820410549836072420489/1000000000000000000000000000000)
  mhi := (22795798992806833441424721119097/500000000000000000000000000000)
  cells := [(80,163),(99,146),(130,187),(130,188),(130,189)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 93

theorem band425_checked : band425.check rectangle=true := by decide +kernel
#print axioms band425_checked

def band426 : Band CellKey where
  qlo := (95749/180624)
  qhi := (47887/90312)
  mlo := (27346127341449662747718587508091/1000000000000000000000000000000)
  mhi := (22795798992806833441424721119097/500000000000000000000000000000)
  cells := [(99,146),(130,187),(130,188),(130,189)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 93

theorem band426_checked : band426.check rectangle=true := by decide +kernel
#print axioms band426_checked

def band427 : Band CellKey where
  qlo := (95749/180624)
  qhi := (47887/90312)
  mlo := (6977977321611293252866122329651/200000000000000000000000000000)
  mhi := (22795798992806833441424721119097/500000000000000000000000000000)
  cells := [(130,187),(130,188),(130,189)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 93

theorem band427_checked : band427.check rectangle=true := by decide +kernel
#print axioms band427_checked

def band428 : Band CellKey where
  qlo := (47887/90312)
  qhi := (31933/60208)
  mlo := (16969028904268311777784736792659/1000000000000000000000000000000)
  mhi := (22795798992806833441424721119097/500000000000000000000000000000)
  cells := [(59,184),(99,147),(130,190),(130,191)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 93

theorem band428_checked : band428.check rectangle=true := by decide +kernel
#print axioms band428_checked

def band429 : Band CellKey where
  qlo := (47887/90312)
  qhi := (31933/60208)
  mlo := (11312685936178874518523157861773/500000000000000000000000000000)
  mhi := (22795798992806833441424721119097/500000000000000000000000000000)
  cells := [(80,164),(99,147),(130,190),(130,191)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 93

theorem band429_checked : band429.check rectangle=true := by decide +kernel
#print axioms band429_checked

def band430 : Band CellKey where
  qlo := (47887/90312)
  qhi := (31933/60208)
  mlo := (13669495506216140043215482416309/500000000000000000000000000000)
  mhi := (22795798992806833441424721119097/500000000000000000000000000000)
  cells := [(99,147),(130,190),(130,191)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 93

theorem band430_checked : band430.check rectangle=true := by decide +kernel
#print axioms band430_checked

def band431 : Band CellKey where
  qlo := (47887/90312)
  qhi := (31933/60208)
  mlo := (8955876366141608993830833307237/250000000000000000000000000000)
  mhi := (22795798992806833441424721119097/500000000000000000000000000000)
  cells := [(130,190),(130,191)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 93

theorem band431_checked : band431.check rectangle=true := by decide +kernel
#print axioms band431_checked

end ForestUnimodality.IntermediateBridgeCoverData

