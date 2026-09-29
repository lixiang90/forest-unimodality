import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band368 : Band CellKey where
  qlo := (94503/178928)
  qhi := (28/53)
  mlo := (8517857142857142857142857142857/500000000000000000000000000000)
  mhi := (45686726706331366712396122639749/1000000000000000000000000000000)
  cells := [(59,169),(99,132),(130,145),(130,146),(130,147)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 89

theorem band368_checked : band368.check rectangle=true := by decide +kernel
#print axioms band368_checked

def band369 : Band CellKey where
  qlo := (94503/178928)
  qhi := (28/53)
  mlo := (4542857142857142857142857142857/200000000000000000000000000000)
  mhi := (45686726706331366712396122639749/1000000000000000000000000000000)
  cells := [(80,149),(99,132),(130,145),(130,146),(130,147)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 89

theorem band369_checked : band369.check rectangle=true := by decide +kernel
#print axioms band369_checked

def band370 : Band CellKey where
  qlo := (94503/178928)
  qhi := (28/53)
  mlo := (6861607142857142857142857142857/250000000000000000000000000000)
  mhi := (45686726706331366712396122639749/1000000000000000000000000000000)
  cells := [(99,132),(130,145),(130,146),(130,147)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 89

theorem band370_checked : band370.check rectangle=true := by decide +kernel
#print axioms band370_checked

def band371 : Band CellKey where
  qlo := (94503/178928)
  qhi := (28/53)
  mlo := (35017857142857142857142857142857/1000000000000000000000000000000)
  mhi := (45686726706331366712396122639749/1000000000000000000000000000000)
  cells := [(130,145),(130,146),(130,147)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 89

theorem band371_checked : band371.check rectangle=true := by decide +kernel
#print axioms band371_checked

def band372 : Band CellKey where
  qlo := (28/53)
  qhi := (95449/180624)
  mlo := (2128906536474976165281983048539/125000000000000000000000000000)
  mhi := (11415764701173436222568165100187/250000000000000000000000000000)
  cells := [(59,170),(99,133),(130,148),(130,149),(130,150)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 90

theorem band372_checked : band372.check rectangle=true := by decide +kernel
#print axioms band372_checked

def band373 : Band CellKey where
  qlo := (28/53)
  qhi := (95449/180624)
  mlo := (11354168194533206214837242925541/500000000000000000000000000000)
  mhi := (11415764701173436222568165100187/250000000000000000000000000000)
  cells := [(80,150),(99,133),(130,148),(130,149),(130,150)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 90

theorem band373_checked : band373.check rectangle=true := by decide +kernel
#print axioms band373_checked

def band374 : Band CellKey where
  qlo := (28/53)
  qhi := (95449/180624)
  mlo := (13719619901727624176261668535029/500000000000000000000000000000)
  mhi := (11415764701173436222568165100187/250000000000000000000000000000)
  cells := [(99,133),(130,148),(130,149),(130,150)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 90

theorem band374_checked : band374.check rectangle=true := by decide +kernel
#print axioms band374_checked

def band375 : Band CellKey where
  qlo := (28/53)
  qhi := (95449/180624)
  mlo := (35008685266477385829081499020419/1000000000000000000000000000000)
  mhi := (11415764701173436222568165100187/250000000000000000000000000000)
  cells := [(130,148),(130,149),(130,150)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 90

theorem band375_checked : band375.check rectangle=true := by decide +kernel
#print axioms band375_checked

def band376 : Band CellKey where
  qlo := (95449/180624)
  qhi := (47737/90312)
  mlo := (8513396317321993422292980287827/500000000000000000000000000000)
  mhi := (11415764701173436222568165100187/250000000000000000000000000000)
  cells := [(59,171),(99,134),(130,151),(130,152),(130,153)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 90

theorem band376_checked : band376.check rectangle=true := by decide +kernel
#print axioms band376_checked

def band377 : Band CellKey where
  qlo := (95449/180624)
  qhi := (47737/90312)
  mlo := (11351195089762657896390640383769/500000000000000000000000000000)
  mhi := (11415764701173436222568165100187/250000000000000000000000000000)
  cells := [(80,151),(99,134),(130,151),(130,152),(130,153)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 90

theorem band377_checked : band377.check rectangle=true := by decide +kernel
#print axioms band377_checked

def band378 : Band CellKey where
  qlo := (95449/180624)
  qhi := (47737/90312)
  mlo := (27432054800259756582944047594109/1000000000000000000000000000000)
  mhi := (11415764701173436222568165100187/250000000000000000000000000000)
  cells := [(99,134),(130,151),(130,152),(130,153)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 90

theorem band378_checked : band378.check rectangle=true := by decide +kernel
#print axioms band378_checked

def band379 : Band CellKey where
  qlo := (95449/180624)
  qhi := (47737/90312)
  mlo := (17499759096717430923602237258311/500000000000000000000000000000)
  mhi := (11415764701173436222568165100187/250000000000000000000000000000)
  cells := [(130,151),(130,152),(130,153)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 90

theorem band379_checked : band379.check rectangle=true := by decide +kernel
#print axioms band379_checked

def band380 : Band CellKey where
  qlo := (47737/90312)
  qhi := (31833/60208)
  mlo := (4255583828102912072377721232683/250000000000000000000000000000)
  mhi := (11415764701173436222568165100187/250000000000000000000000000000)
  cells := [(59,172),(99,135),(130,154),(130,155),(130,156)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 90

theorem band380_checked : band380.check rectangle=true := by decide +kernel
#print axioms band380_checked

def band381 : Band CellKey where
  qlo := (47737/90312)
  qhi := (31833/60208)
  mlo := (22696447083215531052681179907643/1000000000000000000000000000000)
  mhi := (11415764701173436222568165100187/250000000000000000000000000000)
  cells := [(80,152),(99,135),(130,154),(130,155),(130,156)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 90

theorem band381_checked : band381.check rectangle=true := by decide +kernel
#print axioms band381_checked

def band382 : Band CellKey where
  qlo := (47737/90312)
  qhi := (31833/60208)
  mlo := (27424873558885433355323092388401/1000000000000000000000000000000)
  mhi := (11415764701173436222568165100187/250000000000000000000000000000)
  cells := [(99,135),(130,154),(130,155),(130,156)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 90

theorem band382_checked : band382.check rectangle=true := by decide +kernel
#print axioms band382_checked

def band383 : Band CellKey where
  qlo := (47737/90312)
  qhi := (31833/60208)
  mlo := (2186897244997329814971884522351/62500000000000000000000000000)
  mhi := (11415764701173436222568165100187/250000000000000000000000000000)
  cells := [(130,154),(130,155),(130,156)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 90

theorem band383_checked : band383.check rectangle=true := by decide +kernel
#print axioms band383_checked

end ForestUnimodality.IntermediateBridgeCoverData

