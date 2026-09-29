import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band400 : Band CellKey where
  qlo := (95599/180624)
  qhi := (11953/22578)
  mlo := (8500041830502802643687777127081/500000000000000000000000000000)
  mhi := (45639201208552414760621022023893/1000000000000000000000000000000)
  cells := [(59,177),(99,140),(130,169),(130,170),(130,171)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 91

theorem band400_checked : band400.check rectangle=true := by decide +kernel
#print axioms band400_checked

def band401 : Band CellKey where
  qlo := (95599/180624)
  qhi := (11953/22578)
  mlo := (2833347276834267547895925709027/125000000000000000000000000000)
  mhi := (45639201208552414760621022023893/1000000000000000000000000000000)
  cells := [(80,157),(99,140),(130,169),(130,170),(130,171)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 91

theorem band401_checked : band401.check rectangle=true := by decide +kernel
#print axioms band401_checked

def band402 : Band CellKey where
  qlo := (95599/180624)
  qhi := (11953/22578)
  mlo := (27389023676064586296327281853927/1000000000000000000000000000000)
  mhi := (45639201208552414760621022023893/1000000000000000000000000000000)
  cells := [(99,140),(130,169),(130,170),(130,171)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 91

theorem band402_checked : band402.check rectangle=true := by decide +kernel
#print axioms band402_checked

def band403 : Band CellKey where
  qlo := (95599/180624)
  qhi := (11953/22578)
  mlo := (17472308207144649878691541872333/500000000000000000000000000000)
  mhi := (45639201208552414760621022023893/1000000000000000000000000000000)
  cells := [(130,169),(130,170),(130,171)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 91

theorem band403_checked : band403.check rectangle=true := by decide +kernel
#print axioms band403_checked

def band404 : Band CellKey where
  qlo := (11953/22578)
  qhi := (31883/60208)
  mlo := (4248910077470752438603644575479/250000000000000000000000000000)
  mhi := (182461523871945710490940864121/4000000000000000000000000000)
  cells := [(59,178),(99,141),(130,172),(130,173),(130,174)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 92

theorem band404_checked : band404.check rectangle=true := by decide +kernel
#print axioms band404_checked

def band405 : Band CellKey where
  qlo := (11953/22578)
  qhi := (31883/60208)
  mlo := (22660853746510679672552771069221/1000000000000000000000000000000)
  mhi := (182461523871945710490940864121/4000000000000000000000000000)
  cells := [(80,158),(99,141),(130,172),(130,173),(130,174)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 92

theorem band405_checked : band405.check rectangle=true := by decide +kernel
#print axioms band405_checked

def band406 : Band CellKey where
  qlo := (11953/22578)
  qhi := (31883/60208)
  mlo := (27381864943700404604334598375309/1000000000000000000000000000000)
  mhi := (182461523871945710490940864121/4000000000000000000000000000)
  cells := [(99,141),(130,172),(130,173),(130,174)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 92

theorem band406_checked : band406.check rectangle=true := by decide +kernel
#print axioms band406_checked

def band407 : Band CellKey where
  qlo := (11953/22578)
  qhi := (31883/60208)
  mlo := (698709657184079289903710441301/20000000000000000000000000000)
  mhi := (182461523871945710490940864121/4000000000000000000000000000)
  cells := [(130,172),(130,173),(130,174)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 92

theorem band407_checked : band407.check rectangle=true := by decide +kernel
#print axioms band407_checked

def band408 : Band CellKey where
  qlo := (31883/60208)
  qhi := (47837/90312)
  mlo := (8495599640445680122081234191107/500000000000000000000000000000)
  mhi := (182461523871945710490940864121/4000000000000000000000000000)
  cells := [(59,179),(99,142),(130,175),(130,176),(130,177)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 92

theorem band408_checked : band408.check rectangle=true := by decide +kernel
#print axioms band408_checked

def band409 : Band CellKey where
  qlo := (31883/60208)
  qhi := (47837/90312)
  mlo := (11327466187260906829441645588143/500000000000000000000000000000)
  mhi := (182461523871945710490940864121/4000000000000000000000000000)
  cells := [(80,159),(99,142),(130,175),(130,176),(130,177)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 92

theorem band409_checked : band409.check rectangle=true := by decide +kernel
#print axioms band409_checked

def band410 : Band CellKey where
  qlo := (31883/60208)
  qhi := (47837/90312)
  mlo := (6843677488136797876120994209503/250000000000000000000000000000)
  mhi := (182461523871945710490940864121/4000000000000000000000000000)
  cells := [(99,142),(130,175),(130,176),(130,177)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 92

theorem band410_checked : band410.check rectangle=true := by decide +kernel
#print axioms band410_checked

def band411 : Band CellKey where
  qlo := (31883/60208)
  qhi := (47837/90312)
  mlo := (17463177038693898028722536948387/500000000000000000000000000000)
  mhi := (182461523871945710490940864121/4000000000000000000000000000)
  cells := [(130,175),(130,176),(130,177)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 92

theorem band411_checked : band411.check rectangle=true := by decide +kernel
#print axioms band411_checked

def band412 : Band CellKey where
  qlo := (47837/90312)
  qhi := (95699/180624)
  mlo := (8493380286105392950814533067221/500000000000000000000000000000)
  mhi := (182461523871945710490940864121/4000000000000000000000000000)
  cells := [(59,180),(99,143),(130,178),(130,179),(130,180)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 92

theorem band412_checked : band412.check rectangle=true := by decide +kernel
#print axioms band412_checked

def band413 : Band CellKey where
  qlo := (47837/90312)
  qhi := (95699/180624)
  mlo := (22649014096281047868838754845923/1000000000000000000000000000000)
  mhi := (182461523871945710490940864121/4000000000000000000000000000)
  cells := [(80,160),(99,143),(130,178),(130,179),(130,180)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 92

theorem band413_checked : band413.check rectangle=true := by decide +kernel
#print axioms band413_checked

def band414 : Band CellKey where
  qlo := (47837/90312)
  qhi := (95699/180624)
  mlo := (27367558699672932841513495438823/1000000000000000000000000000000)
  mhi := (182461523871945710490940864121/4000000000000000000000000000)
  cells := [(99,143),(130,178),(130,179),(130,180)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 92

theorem band414_checked : band414.check rectangle=true := by decide +kernel
#print axioms band414_checked

def band415 : Band CellKey where
  qlo := (47837/90312)
  qhi := (95699/180624)
  mlo := (4364653758137493599724135048433/125000000000000000000000000000)
  mhi := (182461523871945710490940864121/4000000000000000000000000000)
  cells := [(130,178),(130,179),(130,180)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 92

theorem band415_checked : band415.check rectangle=true := by decide +kernel
#print axioms band415_checked

end ForestUnimodality.IntermediateBridgeCoverData

