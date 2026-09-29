import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band432 : Band CellKey where
  qlo := (31933/60208)
  qhi := (113/213)
  mlo := (8482300884955752212389380530973/500000000000000000000000000000)
  mhi := (22795798992806833441424721119097/500000000000000000000000000000)
  cells := [(59,185),(99,148),(130,192),(130,193)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 93

theorem band432_checked : band432.check rectangle=true := by decide +kernel
#print axioms band432_checked

def band433 : Band CellKey where
  qlo := (31933/60208)
  qhi := (113/213)
  mlo := (22619469026548672566371681415929/1000000000000000000000000000000)
  mhi := (22795798992806833441424721119097/500000000000000000000000000000)
  cells := [(80,165),(99,148),(130,192),(130,193)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 93

theorem band433_checked : band433.check rectangle=true := by decide +kernel
#print axioms band433_checked

def band434 : Band CellKey where
  qlo := (31933/60208)
  qhi := (113/213)
  mlo := (27331858407079646017699115044247/1000000000000000000000000000000)
  mhi := (22795798992806833441424721119097/500000000000000000000000000000)
  cells := [(99,148),(130,192),(130,193)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 93

theorem band434_checked : band434.check rectangle=true := by decide +kernel
#print axioms band434_checked

def band435 : Band CellKey where
  qlo := (31933/60208)
  qhi := (113/213)
  mlo := (35814159292035398230088495575221/1000000000000000000000000000000)
  mhi := (22795798992806833441424721119097/500000000000000000000000000000)
  cells := [(130,192),(130,193)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 93

theorem band435_checked : band435.check rectangle=true := by decide +kernel
#print axioms band435_checked

def band436 : Band CellKey where
  qlo := (113/213)
  qhi := (8069/15194)
  mlo := (3389416284545792539348122443921/200000000000000000000000000000)
  mhi := (45568296132471849000728449201073/1000000000000000000000000000000)
  cells := [(59,186),(99,149),(130,194),(130,195),(130,196)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 94

theorem band436_checked : band436.check rectangle=true := by decide +kernel
#print axioms band436_checked

def band437 : Band CellKey where
  qlo := (113/213)
  qhi := (8069/15194)
  mlo := (11298054281819308464493741479737/500000000000000000000000000000)
  mhi := (45568296132471849000728449201073/1000000000000000000000000000000)
  cells := [(80,166),(99,149),(130,194),(130,195),(130,196)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 94

theorem band437_checked : band437.check rectangle=true := by decide +kernel
#print axioms band437_checked

def band438 : Band CellKey where
  qlo := (113/213)
  qhi := (8069/15194)
  mlo := (27303631181063328789193208576031/1000000000000000000000000000000)
  mhi := (45568296132471849000728449201073/1000000000000000000000000000000)
  cells := [(99,149),(130,194),(130,195),(130,196)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 94

theorem band438_checked : band438.check rectangle=true := by decide +kernel
#print axioms band438_checked

def band439 : Band CellKey where
  qlo := (113/213)
  qhi := (8069/15194)
  mlo := (17888585946213905068781757342917/500000000000000000000000000000)
  mhi := (45568296132471849000728449201073/1000000000000000000000000000000)
  cells := [(130,194),(130,195),(130,196)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 94

theorem band439_checked : band439.check rectangle=true := by decide +kernel
#print axioms band439_checked

def band440 : Band CellKey where
  qlo := (8069/15194)
  qhi := (12116/22791)
  mlo := (16929597226807527236711786068009/1000000000000000000000000000000)
  mhi := (22772404047499532422330823988793/500000000000000000000000000000)
  cells := [(59,187),(99,150),(130,197),(130,198),(130,199)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 95

theorem band440_checked : band440.check rectangle=true := by decide +kernel
#print axioms band440_checked

def band441 : Band CellKey where
  qlo := (8069/15194)
  qhi := (12116/22791)
  mlo := (4514559260482007263123142951469/200000000000000000000000000000)
  mhi := (22772404047499532422330823988793/500000000000000000000000000000)
  cells := [(80,167),(99,150),(130,197),(130,198),(130,199)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 95

theorem band441_checked : band441.check rectangle=true := by decide +kernel
#print axioms band441_checked

def band442 : Band CellKey where
  qlo := (8069/15194)
  qhi := (12116/22791)
  mlo := (1704716387421591284252228458237/62500000000000000000000000000)
  mhi := (22772404047499532422330823988793/500000000000000000000000000000)
  cells := [(99,150),(130,197),(130,198),(130,199)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 95

theorem band442_checked : band442.check rectangle=true := by decide +kernel
#print axioms band442_checked

def band443 : Band CellKey where
  qlo := (8069/15194)
  qhi := (12116/22791)
  mlo := (35740260812149224166391548365797/1000000000000000000000000000000)
  mhi := (22772404047499532422330823988793/500000000000000000000000000000)
  cells := [(130,197),(130,198),(130,199)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 95

theorem band443_checked : band443.check rectangle=true := by decide +kernel
#print axioms band443_checked

def band444 : Band CellKey where
  qlo := (12116/22791)
  qhi := (24257/45582)
  mlo := (845607453518571958609885806159/50000000000000000000000000000)
  mhi := (45521356340581298953754355888939/1000000000000000000000000000000)
  cells := [(59,188),(99,151),(130,200),(130,201),(130,202)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 96

theorem band444_checked : band444.check rectangle=true := by decide +kernel
#print axioms band444_checked

def band445 : Band CellKey where
  qlo := (12116/22791)
  qhi := (24257/45582)
  mlo := (22549532093828585562930288164241/1000000000000000000000000000000)
  mhi := (45521356340581298953754355888939/1000000000000000000000000000000)
  cells := [(80,168),(99,151),(130,200),(130,201),(130,202)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 96

theorem band445_checked : band445.check rectangle=true := by decide +kernel
#print axioms band445_checked

def band446 : Band CellKey where
  qlo := (12116/22791)
  qhi := (24257/45582)
  mlo := (13623675640021437110937049099229/500000000000000000000000000000)
  mhi := (45521356340581298953754355888939/1000000000000000000000000000000)
  cells := [(99,151),(130,200),(130,201),(130,202)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 96

theorem band446_checked : band446.check rectangle=true := by decide +kernel
#print axioms band446_checked

def band447 : Band CellKey where
  qlo := (12116/22791)
  qhi := (24257/45582)
  mlo := (2231464113451787112998309766253/62500000000000000000000000000)
  mhi := (45521356340581298953754355888939/1000000000000000000000000000000)
  cells := [(130,200),(130,201),(130,202)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 96

theorem band447_checked : band447.check rectangle=true := by decide +kernel
#print axioms band447_checked

end ForestUnimodality.IntermediateBridgeCoverData

