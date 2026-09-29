import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band160 : Band CellKey where
  qlo := (4487/9312)
  qhi := (8999/18624)
  mlo := (17591287920880097788643182575841/1000000000000000000000000000000)
  mhi := (10994554950550061117901989109901/250000000000000000000000000000)
  cells := [(59,50),(80,44),(99,45),(130,43),(130,44)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 40

theorem band160_checked : band160.check rectangle=true := by decide +kernel
#print axioms band160_checked

def band161 : Band CellKey where
  qlo := (4487/9312)
  qhi := (8999/18624)
  mlo := (4553039226580731192354706078453/200000000000000000000000000000)
  mhi := (10994554950550061117901989109901/250000000000000000000000000000)
  cells := [(80,44),(99,45),(130,43),(130,44)]
  lowerOrder := 80
  orderCap := 98
  rank := 22
  parentStrip := 40

theorem band161_checked : band161.check rectangle=true := by decide +kernel
#print axioms band161_checked

def band162 : Band CellKey where
  qlo := (4487/9312)
  qhi := (8999/18624)
  mlo := (27939104344927214134903878208689/1000000000000000000000000000000)
  mhi := (10994554950550061117901989109901/250000000000000000000000000000)
  cells := [(99,45),(130,43),(130,44)]
  lowerOrder := 99
  orderCap := 129
  rank := 27
  parentStrip := 40

theorem band162_checked : band162.check rectangle=true := by decide +kernel
#print axioms band162_checked

def band163 : Band CellKey where
  qlo := (4487/9312)
  qhi := (8999/18624)
  mlo := (17073897099677741971330147794199/500000000000000000000000000000)
  mhi := (10994554950550061117901989109901/250000000000000000000000000000)
  cells := [(130,43),(130,44)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 40

theorem band163_checked : band163.check rectangle=true := by decide +kernel
#print axioms band163_checked

def band164 : Band CellKey where
  qlo := (8999/18624)
  qhi := (47/97)
  mlo := (4385638297872340425531914893617/250000000000000000000000000000)
  mhi := (4385638297872340425531914893617/100000000000000000000000000000)
  cells := [(59,52),(80,45),(99,46),(130,45),(130,46)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 41

theorem band164_checked : band164.check rectangle=true := by decide +kernel
#print axioms band164_checked

def band165 : Band CellKey where
  qlo := (8999/18624)
  qhi := (47/97)
  mlo := (22702127659574468085106382978723/1000000000000000000000000000000)
  mhi := (4385638297872340425531914893617/100000000000000000000000000000)
  cells := [(80,45),(99,46),(130,45),(130,46)]
  lowerOrder := 80
  orderCap := 98
  rank := 22
  parentStrip := 41

theorem band165_checked : band165.check rectangle=true := by decide +kernel
#print axioms band165_checked

def band166 : Band CellKey where
  qlo := (8999/18624)
  qhi := (47/97)
  mlo := (13930851063829787234042553191489/500000000000000000000000000000)
  mhi := (4385638297872340425531914893617/100000000000000000000000000000)
  cells := [(99,46),(130,45),(130,46)]
  lowerOrder := 99
  orderCap := 129
  rank := 27
  parentStrip := 41

theorem band166_checked : band166.check rectangle=true := by decide +kernel
#print axioms band166_checked

def band167 : Band CellKey where
  qlo := (8999/18624)
  qhi := (47/97)
  mlo := (6810638297872340425531914893617/200000000000000000000000000000)
  mhi := (4385638297872340425531914893617/100000000000000000000000000000)
  cells := [(130,45),(130,46)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 41

theorem band167_checked : band167.check rectangle=true := by decide +kernel
#print axioms band167_checked

def band168 : Band CellKey where
  qlo := (47/97)
  qhi := (9237/19012)
  mlo := (2186884269784562087257767673487/125000000000000000000000000000)
  mhi := (43737685395691241745155353469741/1000000000000000000000000000000)
  cells := [(59,54),(59,55),(59,56),(99,47),(130,47),(130,48)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 42

theorem band168_checked : band168.check rectangle=true := by decide +kernel
#print axioms band168_checked

def band169 : Band CellKey where
  qlo := (47/97)
  qhi := (9237/19012)
  mlo := (4528136840965681498321966006279/200000000000000000000000000000)
  mhi := (43737685395691241745155353469741/1000000000000000000000000000000)
  cells := [(80,46),(80,47),(80,48),(80,49),(80,50),(99,47),(130,47),(130,48)]
  lowerOrder := 80
  orderCap := 98
  rank := 22
  parentStrip := 42

theorem band169_checked : band169.check rectangle=true := by decide +kernel
#print axioms band169_checked

def band170 : Band CellKey where
  qlo := (47/97)
  qhi := (9237/19012)
  mlo := (13893147125690159142578759337447/500000000000000000000000000000)
  mhi := (43737685395691241745155353469741/1000000000000000000000000000000)
  cells := [(99,47),(130,47),(130,48)]
  lowerOrder := 99
  orderCap := 129
  rank := 27
  parentStrip := 42

theorem band170_checked : band170.check rectangle=true := by decide +kernel
#print axioms band170_checked

def band171 : Band CellKey where
  qlo := (47/97)
  qhi := (9237/19012)
  mlo := (33961026307242611237414745047093/1000000000000000000000000000000)
  mhi := (43737685395691241745155353469741/1000000000000000000000000000000)
  cells := [(130,47),(130,48)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 42

theorem band171_checked : band171.check rectangle=true := by decide +kernel
#print axioms band171_checked

def band172 : Band CellKey where
  qlo := (9237/19012)
  qhi := (4631/9506)
  mlo := (3489570287194990282876268624487/200000000000000000000000000000)
  mhi := (43854838188538453092064677403687/1000000000000000000000000000000)
  cells := [(59,57),(59,58),(59,59),(99,48),(130,49),(130,50)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 43

theorem band172_checked : band172.check rectangle=true := by decide +kernel
#print axioms band172_checked

def band173 : Band CellKey where
  qlo := (9237/19012)
  qhi := (4631/9506)
  mlo := (5644893111638954869358669833729/250000000000000000000000000000)
  mhi := (43854838188538453092064677403687/1000000000000000000000000000000)
  cells := [(80,51),(80,52),(80,53),(80,54),(80,55),(99,48),(130,49),(130,50)]
  lowerOrder := 80
  orderCap := 98
  rank := 22
  parentStrip := 43

theorem band173_checked : band173.check rectangle=true := by decide +kernel
#print axioms band173_checked

def band174 : Band CellKey where
  qlo := (9237/19012)
  qhi := (4631/9506)
  mlo := (27711293457136687540488015547397/1000000000000000000000000000000)
  mhi := (43854838188538453092064677403687/1000000000000000000000000000000)
  cells := [(99,48),(130,49),(130,50)]
  lowerOrder := 99
  orderCap := 129
  rank := 27
  parentStrip := 43

theorem band174_checked : band174.check rectangle=true := by decide +kernel
#print axioms band174_checked

def band175 : Band CellKey where
  qlo := (9237/19012)
  qhi := (4631/9506)
  mlo := (270954869358669833729216152019/8000000000000000000000000000)
  mhi := (43854838188538453092064677403687/1000000000000000000000000000000)
  cells := [(130,49),(130,50)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 43

theorem band175_checked : band175.check rectangle=true := by decide +kernel
#print axioms band175_checked

end ForestUnimodality.IntermediateBridgeCoverData

