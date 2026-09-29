import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band320 : Band CellKey where
  qlo := (2294/4389)
  qhi := (1531/2926)
  mlo := (16244937949052906596995427824951/1000000000000000000000000000000)
  mhi := (45906481840676206727175383778233/1000000000000000000000000000000)
  cells := [(59,152),(59,153),(99,112),(99,113),(130,117),(130,118)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 80

theorem band320_checked : band320.check rectangle=true := by decide +kernel
#print axioms band320_checked

def band321 : Band CellKey where
  qlo := (2294/4389)
  qhi := (1531/2926)
  mlo := (5494611365120836054866100587851/250000000000000000000000000000)
  mhi := (45906481840676206727175383778233/1000000000000000000000000000000)
  cells := [(80,123),(80,124),(99,112),(99,113),(130,117),(130,118)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 80

theorem band321_checked : band321.check rectangle=true := by decide +kernel
#print axioms band321_checked

def band322 : Band CellKey where
  qlo := (2294/4389)
  qhi := (1531/2926)
  mlo := (27711952971913781841933376877857/1000000000000000000000000000000)
  mhi := (45906481840676206727175383778233/1000000000000000000000000000000)
  cells := [(99,112),(99,113),(130,117),(130,118)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 80

theorem band322_checked : band322.check rectangle=true := by decide +kernel
#print axioms band322_checked

def band323 : Band CellKey where
  qlo := (2294/4389)
  qhi := (1531/2926)
  mlo := (4419578706727629000653167864141/125000000000000000000000000000)
  mhi := (45906481840676206727175383778233/1000000000000000000000000000000)
  cells := [(130,117),(130,118)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 80

theorem band323_checked : band323.check rectangle=true := by decide +kernel
#print axioms band323_checked

def band324 : Band CellKey where
  qlo := (1531/2926)
  qhi := (11/21)
  mlo := (2028409090909090909090909090909/125000000000000000000000000000)
  mhi := (9176308442188291735524221078711/200000000000000000000000000000)
  cells := [(59,154),(59,155),(99,114),(99,115),(130,119),(130,120)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 81

theorem band324_checked : band324.check rectangle=true := by decide +kernel
#print axioms band324_checked

def band325 : Band CellKey where
  qlo := (1531/2926)
  qhi := (11/21)
  mlo := (4390909090909090909090909090909/200000000000000000000000000000)
  mhi := (9176308442188291735524221078711/200000000000000000000000000000)
  cells := [(80,125),(80,126),(99,114),(99,115),(130,119),(130,120)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 81

theorem band325_checked : band325.check rectangle=true := by decide +kernel
#print axioms band325_checked

def band326 : Band CellKey where
  qlo := (1531/2926)
  qhi := (11/21)
  mlo := (13840909090909090909090909090909/500000000000000000000000000000)
  mhi := (9176308442188291735524221078711/200000000000000000000000000000)
  cells := [(99,114),(99,115),(130,119),(130,120)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 81

theorem band326_checked : band326.check rectangle=true := by decide +kernel
#print axioms band326_checked

def band327 : Band CellKey where
  qlo := (1531/2926)
  qhi := (11/21)
  mlo := (35318181818181818181818181818181/1000000000000000000000000000000)
  mhi := (9176308442188291735524221078711/200000000000000000000000000000)
  cells := [(130,119),(130,120)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 81

theorem band327_checked : band327.check rectangle=true := by decide +kernel
#print axioms band327_checked

def band328 : Band CellKey where
  qlo := (11/21)
  qhi := (1549/2954)
  mlo := (16209812782440284054228534538411/1000000000000000000000000000000)
  mhi := (2866069708594173111194879805027/62500000000000000000000000000)
  cells := [(59,156),(59,157),(99,116),(99,117),(130,121),(130,122)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 82

theorem band328_checked : band328.check rectangle=true := by decide +kernel
#print axioms band328_checked

def band329 : Band CellKey where
  qlo := (11/21)
  qhi := (1549/2954)
  mlo := (21930923176242737249838605551969/1000000000000000000000000000000)
  mhi := (2866069708594173111194879805027/62500000000000000000000000000)
  cells := [(80,127),(80,128),(80,129),(80,130),(99,116),(99,117),(130,121),(130,122)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 82

theorem band329_checked : band329.check rectangle=true := by decide +kernel
#print axioms band329_checked

def band330 : Band CellKey where
  qlo := (11/21)
  qhi := (1549/2954)
  mlo := (13826016785022595222724338282763/500000000000000000000000000000)
  mhi := (2866069708594173111194879805027/62500000000000000000000000000)
  cells := [(99,116),(99,117),(130,121),(130,122)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 82

theorem band330_checked : band330.check rectangle=true := by decide +kernel
#print axioms band330_checked

def band331 : Band CellKey where
  qlo := (11/21)
  qhi := (1549/2954)
  mlo := (17640090380890897353131052291801/500000000000000000000000000000)
  mhi := (2866069708594173111194879805027/62500000000000000000000000000)
  cells := [(130,121),(130,122)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 82

theorem band331_checked : band331.check rectangle=true := by decide +kernel
#print axioms band331_checked

def band332 : Band CellKey where
  qlo := (1549/2954)
  qhi := (2326/4431)
  mlo := (2024048796216680997420464316423/125000000000000000000000000000)
  mhi := (45832491478571493069299522017427/1000000000000000000000000000000)
  cells := [(59,158),(59,159),(99,118),(99,119),(130,123),(130,124)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 83

theorem band332_checked : band332.check rectangle=true := by decide +kernel
#print axioms band332_checked

def band333 : Band CellKey where
  qlo := (1549/2954)
  qhi := (2326/4431)
  mlo := (2738418959587274290627687016337/125000000000000000000000000000)
  mhi := (45832491478571493069299522017427/1000000000000000000000000000000)
  cells := [(80,131),(80,132),(80,133),(80,134),(99,118),(99,119),(130,123),(130,124)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 83

theorem band333_checked : band333.check rectangle=true := by decide +kernel
#print axioms band333_checked

def band334 : Band CellKey where
  qlo := (1549/2954)
  qhi := (2326/4431)
  mlo := (3452789122957867583834909716251/125000000000000000000000000000)
  mhi := (45832491478571493069299522017427/1000000000000000000000000000000)
  cells := [(99,118),(99,119),(130,123),(130,124)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 83

theorem band334_checked : band334.check rectangle=true := by decide +kernel
#print axioms band334_checked

def band335 : Band CellKey where
  qlo := (1549/2954)
  qhi := (2326/4431)
  mlo := (4405282674118658641444539982803/125000000000000000000000000000)
  mhi := (45832491478571493069299522017427/1000000000000000000000000000000)
  cells := [(130,123),(130,124)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 83

theorem band335_checked : band335.check rectangle=true := by decide +kernel
#print axioms band335_checked

end ForestUnimodality.IntermediateBridgeCoverData

