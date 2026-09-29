import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band272 : Band CellKey where
  qlo := (10996/21321)
  qhi := (7339/14214)
  mlo := (2057824635508924921651451151383/125000000000000000000000000000)
  mhi := (46211915148468120987924632699631/1000000000000000000000000000000)
  cells := [(59,128),(59,129),(99,88),(99,89),(130,93),(130,94)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 68

theorem band272_checked : band272.check rectangle=true := by decide +kernel
#print axioms band272_checked

def band273 : Band CellKey where
  qlo := (10996/21321)
  qhi := (7339/14214)
  mlo := (22272925466684834446109824226733/1000000000000000000000000000000)
  mhi := (46211915148468120987924632699631/1000000000000000000000000000000)
  cells := [(80,101),(80,102),(99,88),(99,89),(130,93),(130,94)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 68

theorem band273_checked : band273.check rectangle=true := by decide +kernel
#print axioms band273_checked

def band274 : Band CellKey where
  qlo := (10996/21321)
  qhi := (7339/14214)
  mlo := (13557432892764681836762501703229/500000000000000000000000000000)
  mhi := (46211915148468120987924632699631/1000000000000000000000000000000)
  cells := [(99,88),(99,89),(130,93),(130,94)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 68

theorem band274_checked : band274.check rectangle=true := by decide +kernel
#print axioms band274_checked

def band275 : Band CellKey where
  qlo := (10996/21321)
  qhi := (7339/14214)
  mlo := (35830358359449516282872325929963/1000000000000000000000000000000)
  mhi := (46211915148468120987924632699631/1000000000000000000000000000000)
  cells := [(130,93),(130,94)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 68

theorem band275_checked : band275.check rectangle=true := by decide +kernel
#print axioms band275_checked

def band276 : Band CellKey where
  qlo := (7339/14214)
  qhi := (107/207)
  mlo := (4110981308411214953271028037383/250000000000000000000000000000)
  mhi := (23092865374363363393020367709229/500000000000000000000000000000)
  cells := [(59,130),(59,131),(99,90),(99,91),(130,95),(130,96)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 69

theorem band276_checked : band276.check rectangle=true := by decide +kernel
#print axioms band276_checked

def band277 : Band CellKey where
  qlo := (7339/14214)
  qhi := (107/207)
  mlo := (22247663551401869158878504672897/1000000000000000000000000000000)
  mhi := (23092865374363363393020367709229/500000000000000000000000000000)
  cells := [(80,103),(80,104),(99,90),(99,91),(130,95),(130,96)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 69

theorem band277_checked : band277.check rectangle=true := by decide +kernel
#print axioms band277_checked

def band278 : Band CellKey where
  qlo := (7339/14214)
  qhi := (107/207)
  mlo := (270841121495327102803738317757/10000000000000000000000000000)
  mhi := (23092865374363363393020367709229/500000000000000000000000000000)
  cells := [(99,90),(99,91),(130,95),(130,96)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 69

theorem band278_checked : band278.check rectangle=true := by decide +kernel
#print axioms band278_checked

def band279 : Band CellKey where
  qlo := (7339/14214)
  qhi := (107/207)
  mlo := (35789719626168224299065420560747/1000000000000000000000000000000)
  mhi := (23092865374363363393020367709229/500000000000000000000000000000)
  cells := [(130,95),(130,96)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 69

theorem band279_checked : band279.check rectangle=true := by decide +kernel
#print axioms band279_checked

def band280 : Band CellKey where
  qlo := (107/207)
  qhi := (7427/14352)
  mlo := (821273730981553790224855257843/50000000000000000000000000000)
  mhi := (46160093648285422993522618497939/1000000000000000000000000000000)
  cells := [(59,132),(59,133),(99,92),(99,93),(130,97),(130,98)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 70

theorem band280_checked : band280.check rectangle=true := by decide +kernel
#print axioms band280_checked

def band281 : Band CellKey where
  qlo := (107/207)
  qhi := (7427/14352)
  mlo := (22222700955971455500201965800457/1000000000000000000000000000000)
  mhi := (46160093648285422993522618497939/1000000000000000000000000000000)
  cells := [(80,105),(99,92),(99,93),(130,97),(130,98)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 70

theorem band281_checked : band281.check rectangle=true := by decide +kernel
#print axioms band281_checked

def band282 : Band CellKey where
  qlo := (107/207)
  qhi := (7427/14352)
  mlo := (13526861451460885956644674835061/500000000000000000000000000000)
  mhi := (46160093648285422993522618497939/1000000000000000000000000000000)
  cells := [(99,92),(99,93),(130,97),(130,98)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 70

theorem band282_checked : band282.check rectangle=true := by decide +kernel
#print axioms band282_checked

def band283 : Band CellKey where
  qlo := (107/207)
  qhi := (7427/14352)
  mlo := (35749562407432341456846640635519/1000000000000000000000000000000)
  mhi := (46160093648285422993522618497939/1000000000000000000000000000000)
  cells := [(130,97),(130,98)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 70

theorem band283_checked : band283.check rectangle=true := by decide +kernel
#print axioms band283_checked

def band284 : Band CellKey where
  qlo := (7427/14352)
  qhi := (11153/21528)
  mlo := (8203532681789653008159239666457/500000000000000000000000000000)
  mhi := (5766780988091430933865889808123/125000000000000000000000000000)
  cells := [(59,134),(59,135),(99,94),(99,95),(130,99),(130,100)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 71

theorem band284_checked : band284.check rectangle=true := by decide +kernel
#print axioms band284_checked

def band285 : Band CellKey where
  qlo := (7427/14352)
  qhi := (11153/21528)
  mlo := (11098897157715412893391912489913/500000000000000000000000000000)
  mhi := (5766780988091430933865889808123/125000000000000000000000000000)
  cells := [(80,106),(99,94),(99,95),(130,99),(130,100)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 71

theorem band285_checked : band285.check rectangle=true := by decide +kernel
#print axioms band285_checked

def band286 : Band CellKey where
  qlo := (7427/14352)
  qhi := (11153/21528)
  mlo := (13511700887653546131085806509459/500000000000000000000000000000)
  mhi := (5766780988091430933865889808123/125000000000000000000000000000)
  cells := [(99,94),(99,95),(130,99),(130,100)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 71

theorem band286_checked : band286.check rectangle=true := by decide +kernel
#print axioms band286_checked

def band287 : Band CellKey where
  qlo := (7427/14352)
  qhi := (11153/21528)
  mlo := (7141899040616874383573926297857/200000000000000000000000000000)
  mhi := (5766780988091430933865889808123/125000000000000000000000000000)
  cells := [(130,99),(130,100)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 71

theorem band287_checked : band287.check rectangle=true := by decide +kernel
#print axioms band287_checked

end ForestUnimodality.IntermediateBridgeCoverData

