import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band048 : Band CellKey where
  qlo := (29/85)
  qhi := (89/255)
  mlo := (4297752808988764044943820224719/200000000000000000000000000000)
  mhi := (60884831460674157303370786516853/1000000000000000000000000000000)
  cells := [(59,12),(99,12),(130,12)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 12

theorem band048_checked : band048.check rectangle=true := by decide +kernel
#print axioms band048_checked

def band049 : Band CellKey where
  qlo := (29/85)
  qhi := (89/255)
  mlo := (1432584269662921348314606741573/50000000000000000000000000000)
  mhi := (60884831460674157303370786516853/1000000000000000000000000000000)
  cells := [(80,12),(99,12),(130,12)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 12

theorem band049_checked : band049.check rectangle=true := by decide +kernel
#print axioms band049_checked

def band050 : Band CellKey where
  qlo := (29/85)
  qhi := (89/255)
  mlo := (1432584269662921348314606741573/40000000000000000000000000000)
  mhi := (60884831460674157303370786516853/1000000000000000000000000000000)
  cells := [(99,12),(130,12)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 12

theorem band050_checked : band050.check rectangle=true := by decide +kernel
#print axioms band050_checked

def band051 : Band CellKey where
  qlo := (29/85)
  qhi := (89/255)
  mlo := (4727528089887640449438202247191/100000000000000000000000000000)
  mhi := (60884831460674157303370786516853/1000000000000000000000000000000)
  cells := [(130,12)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 12

theorem band051_checked : band051.check rectangle=true := by decide +kernel
#print axioms band051_checked

def band052 : Band CellKey where
  qlo := (89/255)
  qhi := (91/255)
  mlo := (21016483516483516483516483516483/1000000000000000000000000000000)
  mhi := (59546703296703296703296703296703/1000000000000000000000000000000)
  cells := [(59,13),(99,13),(130,13)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 13

theorem band052_checked : band052.check rectangle=true := by decide +kernel
#print axioms band052_checked

def band053 : Band CellKey where
  qlo := (89/255)
  qhi := (91/255)
  mlo := (14010989010989010989010989010989/500000000000000000000000000000)
  mhi := (59546703296703296703296703296703/1000000000000000000000000000000)
  cells := [(80,13),(99,13),(130,13)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 13

theorem band053_checked : band053.check rectangle=true := by decide +kernel
#print axioms band053_checked

def band054 : Band CellKey where
  qlo := (89/255)
  qhi := (91/255)
  mlo := (2189217032967032967032967032967/62500000000000000000000000000)
  mhi := (59546703296703296703296703296703/1000000000000000000000000000000)
  cells := [(99,13),(130,13)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 13

theorem band054_checked : band054.check rectangle=true := by decide +kernel
#print axioms band054_checked

def band055 : Band CellKey where
  qlo := (89/255)
  qhi := (91/255)
  mlo := (46236263736263736263736263736263/1000000000000000000000000000000)
  mhi := (59546703296703296703296703296703/1000000000000000000000000000000)
  cells := [(130,13)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 13

theorem band055_checked : band055.check rectangle=true := by decide +kernel
#print axioms band055_checked

def band056 : Band CellKey where
  qlo := (91/255)
  qhi := (31/85)
  mlo := (10282258064516129032258064516129/500000000000000000000000000000)
  mhi := (3641633064516129032258064516129/62500000000000000000000000000)
  cells := [(59,14),(99,14),(130,14)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 14

theorem band056_checked : band056.check rectangle=true := by decide +kernel
#print axioms band056_checked

def band057 : Band CellKey where
  qlo := (91/255)
  qhi := (31/85)
  mlo := (27419354838709677419354838709677/1000000000000000000000000000000)
  mhi := (3641633064516129032258064516129/62500000000000000000000000000)
  cells := [(80,14),(99,14),(130,14)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 14

theorem band057_checked : band057.check rectangle=true := by decide +kernel
#print axioms band057_checked

def band058 : Band CellKey where
  qlo := (91/255)
  qhi := (31/85)
  mlo := (4284274193548387096774193548387/125000000000000000000000000000)
  mhi := (3641633064516129032258064516129/62500000000000000000000000000)
  cells := [(99,14),(130,14)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 14

theorem band058_checked : band058.check rectangle=true := by decide +kernel
#print axioms band058_checked

def band059 : Band CellKey where
  qlo := (91/255)
  qhi := (31/85)
  mlo := (45241935483870967741935483870967/1000000000000000000000000000000)
  mhi := (3641633064516129032258064516129/62500000000000000000000000000)
  cells := [(130,14)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 14

theorem band059_checked : band059.check rectangle=true := by decide +kernel
#print axioms band059_checked

def band060 : Band CellKey where
  qlo := (31/85)
  qhi := (19/51)
  mlo := (2516447368421052631578947368421/125000000000000000000000000000)
  mhi := (5703947368421052631578947368421/100000000000000000000000000000)
  cells := [(59,15),(99,15),(130,15)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 15

theorem band060_checked : band060.check rectangle=true := by decide +kernel
#print axioms band060_checked

def band061 : Band CellKey where
  qlo := (31/85)
  qhi := (19/51)
  mlo := (26842105263157894736842105263157/1000000000000000000000000000000)
  mhi := (5703947368421052631578947368421/100000000000000000000000000000)
  cells := [(80,15),(99,15),(130,15)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 15

theorem band061_checked : band061.check rectangle=true := by decide +kernel
#print axioms band061_checked

def band062 : Band CellKey where
  qlo := (31/85)
  qhi := (19/51)
  mlo := (33552631578947368421052631578947/1000000000000000000000000000000)
  mhi := (5703947368421052631578947368421/100000000000000000000000000000)
  cells := [(99,15),(130,15)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 15

theorem band062_checked : band062.check rectangle=true := by decide +kernel
#print axioms band062_checked

def band063 : Band CellKey where
  qlo := (31/85)
  qhi := (19/51)
  mlo := (4428947368421052631578947368421/100000000000000000000000000000)
  mhi := (5703947368421052631578947368421/100000000000000000000000000000)
  cells := [(130,15)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 15

theorem band063_checked : band063.check rectangle=true := by decide +kernel
#print axioms band063_checked

end ForestUnimodality.IntermediateBridgeCoverData

