import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band016 : Band CellKey where
  qlo := (39/140)
  qhi := (2/7)
  mlo := (105/4)
  mhi := (595/8)
  cells := [(59,4),(99,4),(130,4)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 4

theorem band016_checked : band016.check rectangle=true := by decide +kernel
#print axioms band016_checked

def band017 : Band CellKey where
  qlo := (39/140)
  qhi := (2/7)
  mlo := (35/1)
  mhi := (595/8)
  cells := [(80,4),(99,4),(130,4)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 4

theorem band017_checked : band017.check rectangle=true := by decide +kernel
#print axioms band017_checked

def band018 : Band CellKey where
  qlo := (39/140)
  qhi := (2/7)
  mlo := (175/4)
  mhi := (595/8)
  cells := [(99,4),(130,4)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 4

theorem band018_checked : band018.check rectangle=true := by decide +kernel
#print axioms band018_checked

def band019 : Band CellKey where
  qlo := (39/140)
  qhi := (2/7)
  mlo := (231/4)
  mhi := (595/8)
  cells := [(130,4)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 4

theorem band019_checked : band019.check rectangle=true := by decide +kernel
#print axioms band019_checked

def band020 : Band CellKey where
  qlo := (2/7)
  qhi := (37/126)
  mlo := (1277027027027027027027027027027/50000000000000000000000000000)
  mhi := (2261402027027027027027027027027/31250000000000000000000000000)
  cells := [(59,5),(99,5),(130,5)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 5

theorem band020_checked : band020.check rectangle=true := by decide +kernel
#print axioms band020_checked

def band021 : Band CellKey where
  qlo := (2/7)
  qhi := (37/126)
  mlo := (17027027027027027027027027027027/500000000000000000000000000000)
  mhi := (2261402027027027027027027027027/31250000000000000000000000000)
  cells := [(80,5),(99,5),(130,5)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 5

theorem band021_checked : band021.check rectangle=true := by decide +kernel
#print axioms band021_checked

def band022 : Band CellKey where
  qlo := (2/7)
  qhi := (37/126)
  mlo := (42567567567567567567567567567567/1000000000000000000000000000000)
  mhi := (2261402027027027027027027027027/31250000000000000000000000000)
  cells := [(99,5),(130,5)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 5

theorem band022_checked : band022.check rectangle=true := by decide +kernel
#print axioms band022_checked

def band023 : Band CellKey where
  qlo := (2/7)
  qhi := (37/126)
  mlo := (56189189189189189189189189189189/1000000000000000000000000000000)
  mhi := (2261402027027027027027027027027/31250000000000000000000000000)
  cells := [(130,5)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 5

theorem band023_checked : band023.check rectangle=true := by decide +kernel
#print axioms band023_checked

def band024 : Band CellKey where
  qlo := (37/126)
  qhi := (19/63)
  mlo := (24868421052631578947368421052631/1000000000000000000000000000000)
  mhi := (70460526315789473684210526315789/1000000000000000000000000000000)
  cells := [(59,6),(99,6),(130,6)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 6

theorem band024_checked : band024.check rectangle=true := by decide +kernel
#print axioms band024_checked

def band025 : Band CellKey where
  qlo := (37/126)
  qhi := (19/63)
  mlo := (16578947368421052631578947368421/500000000000000000000000000000)
  mhi := (70460526315789473684210526315789/1000000000000000000000000000000)
  cells := [(80,6),(99,6),(130,6)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 6

theorem band025_checked : band025.check rectangle=true := by decide +kernel
#print axioms band025_checked

def band026 : Band CellKey where
  qlo := (37/126)
  qhi := (19/63)
  mlo := (10361842105263157894736842105263/250000000000000000000000000000)
  mhi := (70460526315789473684210526315789/1000000000000000000000000000000)
  cells := [(99,6),(130,6)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 6

theorem band026_checked : band026.check rectangle=true := by decide +kernel
#print axioms band026_checked

def band027 : Band CellKey where
  qlo := (37/126)
  qhi := (19/63)
  mlo := (54710526315789473684210526315789/1000000000000000000000000000000)
  mhi := (70460526315789473684210526315789/1000000000000000000000000000000)
  cells := [(130,6)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 6

theorem band027_checked : band027.check rectangle=true := by decide +kernel
#print axioms band027_checked

def band028 : Band CellKey where
  qlo := (19/63)
  qhi := (13/42)
  mlo := (24230769230769230769230769230769/1000000000000000000000000000000)
  mhi := (34326923076923076923076923076923/500000000000000000000000000000)
  cells := [(59,7),(99,7),(130,7)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 7

theorem band028_checked : band028.check rectangle=true := by decide +kernel
#print axioms band028_checked

def band029 : Band CellKey where
  qlo := (19/63)
  qhi := (13/42)
  mlo := (8076923076923076923076923076923/250000000000000000000000000000)
  mhi := (34326923076923076923076923076923/500000000000000000000000000000)
  cells := [(80,7),(99,7),(130,7)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 7

theorem band029_checked : band029.check rectangle=true := by decide +kernel
#print axioms band029_checked

def band030 : Band CellKey where
  qlo := (19/63)
  qhi := (13/42)
  mlo := (8076923076923076923076923076923/200000000000000000000000000000)
  mhi := (34326923076923076923076923076923/500000000000000000000000000000)
  cells := [(99,7),(130,7)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 7

theorem band030_checked : band030.check rectangle=true := by decide +kernel
#print axioms band030_checked

def band031 : Band CellKey where
  qlo := (19/63)
  qhi := (13/42)
  mlo := (13326923076923076923076923076923/250000000000000000000000000000)
  mhi := (34326923076923076923076923076923/500000000000000000000000000000)
  cells := [(130,7)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 7

theorem band031_checked : band031.check rectangle=true := by decide +kernel
#print axioms band031_checked

end ForestUnimodality.IntermediateBridgeCoverData

