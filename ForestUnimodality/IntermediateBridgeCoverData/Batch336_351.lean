import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band336 : Band CellKey where
  qlo := (2326/4431)
  qhi := (4657/8862)
  mlo := (16175005368262830148164054112089/1000000000000000000000000000000)
  mhi := (572598840547313770417854953129/12500000000000000000000000000)
  cells := [(59,160),(59,161),(99,120),(99,121),(130,125),(130,126)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 84

theorem band336_checked : band336.check rectangle=true := by decide +kernel
#print axioms band336_checked

def band337 : Band CellKey where
  qlo := (2326/4431)
  qhi := (4657/8862)
  mlo := (85483714032639038007300837449/3906250000000000000000000000)
  mhi := (572598840547313770417854953129/12500000000000000000000000000)
  cells := [(80,135),(80,136),(80,137),(80,138),(99,120),(99,121),(130,125),(130,126)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 84

theorem band337_checked : band337.check rectangle=true := by decide +kernel
#print axioms band337_checked

def band338 : Band CellKey where
  qlo := (2326/4431)
  qhi := (4657/8862)
  mlo := (27592656216448357311573974661799/1000000000000000000000000000000)
  mhi := (572598840547313770417854953129/12500000000000000000000000000)
  cells := [(99,120),(99,121),(130,125),(130,126)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 84

theorem band338_checked : band338.check rectangle=true := by decide +kernel
#print axioms band338_checked

def band339 : Band CellKey where
  qlo := (2326/4431)
  qhi := (4657/8862)
  mlo := (17602211724286021043590294180803/500000000000000000000000000000)
  mhi := (572598840547313770417854953129/12500000000000000000000000000)
  cells := [(130,125),(130,126)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 84

theorem band339_checked : band339.check rectangle=true := by decide +kernel
#print axioms band339_checked

def band340 : Band CellKey where
  qlo := (4657/8862)
  qhi := (111/211)
  mlo := (4277027027027027027027027027027/250000000000000000000000000000)
  mhi := (44710314967764829418944685157/976562500000000000000000000)
  cells := [(59,162),(99,122),(99,123),(130,127),(130,128)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 85

theorem band340_checked : band340.check rectangle=true := by decide +kernel
#print axioms band340_checked

def band341 : Band CellKey where
  qlo := (4657/8862)
  qhi := (111/211)
  mlo := (546509009009009009009009009009/25000000000000000000000000000)
  mhi := (44710314967764829418944685157/976562500000000000000000000)
  cells := [(80,139),(80,140),(80,141),(80,142),(99,122),(99,123),(130,127),(130,128)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 85

theorem band341_checked : band341.check rectangle=true := by decide +kernel
#print axioms band341_checked

def band342 : Band CellKey where
  qlo := (4657/8862)
  qhi := (111/211)
  mlo := (27563063063063063063063063063063/1000000000000000000000000000000)
  mhi := (44710314967764829418944685157/976562500000000000000000000)
  cells := [(99,122),(99,123),(130,127),(130,128)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 85

theorem band342_checked : band342.check rectangle=true := by decide +kernel
#print axioms band342_checked

def band343 : Band CellKey where
  qlo := (4657/8862)
  qhi := (111/211)
  mlo := (17583333333333333333333333333333/500000000000000000000000000000)
  mhi := (44710314967764829418944685157/976562500000000000000000000)
  cells := [(130,127),(130,128)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 85

theorem band343_checked : band343.check rectangle=true := by decide +kernel
#print axioms band343_checked

def band344 : Band CellKey where
  qlo := (111/211)
  qhi := (23557/44732)
  mlo := (4272488007810841788003565819077/250000000000000000000000000000)
  mhi := (22879659858106169142199468725331/500000000000000000000000000000)
  cells := [(59,163),(99,124),(99,125),(130,129),(130,130),(130,131)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 86

theorem band344_checked : band344.check rectangle=true := by decide +kernel
#print axioms band344_checked

def band345 : Band CellKey where
  qlo := (111/211)
  qhi := (23557/44732)
  mlo := (1424162669270280596001188606359/62500000000000000000000000000)
  mhi := (22879659858106169142199468725331/500000000000000000000000000000)
  cells := [(80,143),(99,124),(99,125),(130,129),(130,130),(130,131)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 86

theorem band345_checked : band345.check rectangle=true := by decide +kernel
#print axioms band345_checked

def band346 : Band CellKey where
  qlo := (111/211)
  qhi := (23557/44732)
  mlo := (3441726450736511440336205798701/125000000000000000000000000000)
  mhi := (22879659858106169142199468725331/500000000000000000000000000000)
  cells := [(99,124),(99,125),(130,129),(130,130),(130,131)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 86

theorem band346_checked : band346.check rectangle=true := by decide +kernel
#print axioms band346_checked

def band347 : Band CellKey where
  qlo := (111/211)
  qhi := (23557/44732)
  mlo := (35129345842000254701362652290189/1000000000000000000000000000000)
  mhi := (22879659858106169142199468725331/500000000000000000000000000000)
  cells := [(130,129),(130,130),(130,131)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 86

theorem band347_checked : band347.check rectangle=true := by decide +kernel
#print axioms band347_checked

def band348 : Band CellKey where
  qlo := (23557/44732)
  qhi := (11791/22366)
  mlo := (17071834450004240522432363667203/1000000000000000000000000000000)
  mhi := (22867541805745730174881400393781/500000000000000000000000000000)
  cells := [(59,164),(99,126),(99,127),(130,132),(130,133),(130,134)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 87

theorem band348_checked : band348.check rectangle=true := by decide +kernel
#print axioms band348_checked

def band349 : Band CellKey where
  qlo := (23557/44732)
  qhi := (11791/22366)
  mlo := (22762445933338987363243151556271/1000000000000000000000000000000)
  mhi := (22867541805745730174881400393781/500000000000000000000000000000)
  cells := [(80,144),(99,126),(99,127),(130,132),(130,133),(130,134)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 87

theorem band349_checked : band349.check rectangle=true := by decide +kernel
#print axioms band349_checked

def band350 : Band CellKey where
  qlo := (23557/44732)
  qhi := (11791/22366)
  mlo := (6876155542362819099313035365957/250000000000000000000000000000)
  mhi := (22867541805745730174881400393781/500000000000000000000000000000)
  cells := [(99,126),(99,127),(130,132),(130,133),(130,134)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 87

theorem band350_checked : band350.check rectangle=true := by decide +kernel
#print axioms band350_checked

def band351 : Band CellKey where
  qlo := (23557/44732)
  qhi := (11791/22366)
  mlo := (17546052073615469425833262657959/500000000000000000000000000000)
  mhi := (22867541805745730174881400393781/500000000000000000000000000000)
  cells := [(130,132),(130,133),(130,134)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 87

theorem band351_checked : band351.check rectangle=true := by decide +kernel
#print axioms band351_checked

end ForestUnimodality.IntermediateBridgeCoverData

