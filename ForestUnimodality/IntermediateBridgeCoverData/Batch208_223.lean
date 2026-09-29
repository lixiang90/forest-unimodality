import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band208 : Band CellKey where
  qlo := (197/396)
  qhi := (395/792)
  mlo := (1704303797468354430379746835443/100000000000000000000000000000)
  mhi := (46361753154533187688748955856791/1000000000000000000000000000000)
  cells := [(59,88),(59,89),(59,90),(59,91),(99,58),(130,65)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 52

theorem band208_checked : band208.check rectangle=true := by decide +kernel
#print axioms band208_checked

def band209 : Band CellKey where
  qlo := (197/396)
  qhi := (395/792)
  mlo := (11529113924050632911392405063291/500000000000000000000000000000)
  mhi := (46361753154533187688748955856791/1000000000000000000000000000000)
  cells := [(80,81),(80,82),(99,58),(130,65)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 52

theorem band209_checked : band209.check rectangle=true := by decide +kernel
#print axioms band209_checked

def band210 : Band CellKey where
  qlo := (197/396)
  qhi := (395/792)
  mlo := (7017721518987341772151898734177/250000000000000000000000000000)
  mhi := (46361753154533187688748955856791/1000000000000000000000000000000)
  cells := [(99,58),(130,65)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 52

theorem band210_checked : band210.check rectangle=true := by decide +kernel
#print axioms band210_checked

def band211 : Band CellKey where
  qlo := (197/396)
  qhi := (395/792)
  mlo := (36091139240506329113924050632911/1000000000000000000000000000000)
  mhi := (46361753154533187688748955856791/1000000000000000000000000000000)
  cells := [(130,65)]
  lowerOrder := 130
  orderCap := 169
  rank := 36
  parentStrip := 52

theorem band211_checked : band211.check rectangle=true := by decide +kernel
#print axioms band211_checked

def band212 : Band CellKey where
  qlo := (395/792)
  qhi := (1/2)
  mlo := (17/1)
  mhi := (2330834170886075949367088607593/50000000000000000000000000000)
  cells := [(59,92),(59,93),(59,94),(59,95),(99,59),(130,66),(130,67)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 53

theorem band212_checked : band212.check rectangle=true := by decide +kernel
#print axioms band212_checked

def band213 : Band CellKey where
  qlo := (395/792)
  qhi := (1/2)
  mlo := (23/1)
  mhi := (2330834170886075949367088607593/50000000000000000000000000000)
  cells := [(80,83),(80,84),(80,85),(80,86),(99,59),(130,66),(130,67)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 53

theorem band213_checked : band213.check rectangle=true := by decide +kernel
#print axioms band213_checked

def band214 : Band CellKey where
  qlo := (395/792)
  qhi := (1/2)
  mlo := (28/1)
  mhi := (2330834170886075949367088607593/50000000000000000000000000000)
  cells := [(99,59),(130,66),(130,67)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 53

theorem band214_checked : band214.check rectangle=true := by decide +kernel
#print axioms band214_checked

def band215 : Band CellKey where
  qlo := (395/792)
  qhi := (1/2)
  mlo := (36/1)
  mhi := (2330834170886075949367088607593/50000000000000000000000000000)
  cells := [(130,66),(130,67)]
  lowerOrder := 130
  orderCap := 169
  rank := 36
  parentStrip := 53

theorem band215_checked : band215.check rectangle=true := by decide +kernel
#print axioms band215_checked

def band216 : Band CellKey where
  qlo := (1/2)
  qhi := (405/808)
  mlo := (8479012345679012345679012345679/500000000000000000000000000000)
  mhi := (9374158637037037037037037037037/200000000000000000000000000000)
  cells := [(59,96),(59,97),(59,98),(99,60),(99,61),(130,68),(130,69)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 54

theorem band216_checked : band216.check rectangle=true := by decide +kernel
#print axioms band216_checked

def band217 : Band CellKey where
  qlo := (1/2)
  qhi := (405/808)
  mlo := (22943209876543209876543209876543/1000000000000000000000000000000)
  mhi := (9374158637037037037037037037037/200000000000000000000000000000)
  cells := [(80,87),(99,60),(99,61),(130,68),(130,69)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 54

theorem band217_checked : band217.check rectangle=true := by decide +kernel
#print axioms band217_checked

def band218 : Band CellKey where
  qlo := (1/2)
  qhi := (405/808)
  mlo := (2793086419753086419753086419753/100000000000000000000000000000)
  mhi := (9374158637037037037037037037037/200000000000000000000000000000)
  cells := [(99,60),(99,61),(130,68),(130,69)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 54

theorem band218_checked : band218.check rectangle=true := by decide +kernel
#print axioms band218_checked

def band219 : Band CellKey where
  qlo := (1/2)
  qhi := (405/808)
  mlo := (35911111111111111111111111111111/1000000000000000000000000000000)
  mhi := (9374158637037037037037037037037/200000000000000000000000000000)
  cells := [(130,68),(130,69)]
  lowerOrder := 130
  orderCap := 169
  rank := 36
  parentStrip := 54

theorem band219_checked : band219.check rectangle=true := by decide +kernel
#print axioms band219_checked

def band220 : Band CellKey where
  qlo := (405/808)
  qhi := (203/404)
  mlo := (16916256157635467980295566502463/1000000000000000000000000000000)
  mhi := (91431987593166186364304639039/1953125000000000000000000000)
  cells := [(59,99),(59,100),(59,101),(99,62),(99,63),(130,70),(130,71)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 55

theorem band220_checked : band220.check rectangle=true := by decide +kernel
#print axioms band220_checked

def band221 : Band CellKey where
  qlo := (405/808)
  qhi := (203/404)
  mlo := (11443349753694581280788177339901/500000000000000000000000000000)
  mhi := (91431987593166186364304639039/1953125000000000000000000000)
  cells := [(80,88),(99,62),(99,63),(130,70),(130,71)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 55

theorem band221_checked : band221.check rectangle=true := by decide +kernel
#print axioms band221_checked

def band222 : Band CellKey where
  qlo := (405/808)
  qhi := (203/404)
  mlo := (13931034482758620689655172413793/500000000000000000000000000000)
  mhi := (91431987593166186364304639039/1953125000000000000000000000)
  cells := [(99,62),(99,63),(130,70),(130,71)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 55

theorem band222_checked : band222.check rectangle=true := by decide +kernel
#print axioms band222_checked

def band223 : Band CellKey where
  qlo := (405/808)
  qhi := (203/404)
  mlo := (35822660098522167487684729064039/1000000000000000000000000000000)
  mhi := (91431987593166186364304639039/1953125000000000000000000000)
  cells := [(130,70),(130,71)]
  lowerOrder := 130
  orderCap := 169
  rank := 36
  parentStrip := 55

theorem band223_checked : band223.check rectangle=true := by decide +kernel
#print axioms band223_checked

end ForestUnimodality.IntermediateBridgeCoverData

