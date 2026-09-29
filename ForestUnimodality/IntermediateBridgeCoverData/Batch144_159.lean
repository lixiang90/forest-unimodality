import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band144 : Band CellKey where
  qlo := (869/1824)
  qhi := (581/1216)
  mlo := (16743545611015490533562822719449/1000000000000000000000000000000)
  mhi := (44475043029259896729776247848537/1000000000000000000000000000000)
  cells := [(59,43),(59,44),(99,38),(99,39),(130,36),(130,37)]
  lowerOrder := 59
  orderCap := 79
  rank := 16
  parentStrip := 36

theorem band144_checked : band144.check rectangle=true := by decide +kernel
#print axioms band144_checked

def band145 : Band CellKey where
  qlo := (869/1824)
  qhi := (581/1216)
  mlo := (11511187607573149741824440619621/500000000000000000000000000000)
  mhi := (44475043029259896729776247848537/1000000000000000000000000000000)
  cells := [(80,40),(99,38),(99,39),(130,36),(130,37)]
  lowerOrder := 80
  orderCap := 98
  rank := 22
  parentStrip := 36

theorem band145_checked : band145.check rectangle=true := by decide +kernel
#print axioms band145_checked

def band146 : Band CellKey where
  qlo := (869/1824)
  qhi := (581/1216)
  mlo := (425129087779690189328743545611/15625000000000000000000000000)
  mhi := (44475043029259896729776247848537/1000000000000000000000000000000)
  cells := [(99,38),(99,39),(130,36),(130,37)]
  lowerOrder := 99
  orderCap := 129
  rank := 26
  parentStrip := 36

theorem band146_checked : band146.check rectangle=true := by decide +kernel
#print axioms band146_checked

def band147 : Band CellKey where
  qlo := (869/1824)
  qhi := (581/1216)
  mlo := (2158347676419965576592082616179/62500000000000000000000000000)
  mhi := (44475043029259896729776247848537/1000000000000000000000000000000)
  cells := [(130,36),(130,37)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 36

theorem band147_checked : band147.check rectangle=true := by decide +kernel
#print axioms band147_checked

def band148 : Band CellKey where
  qlo := (581/1216)
  qhi := (23/48)
  mlo := (16695652173913043478260869565217/1000000000000000000000000000000)
  mhi := (2771739130434782608695652173913/62500000000000000000000000000)
  cells := [(59,45),(59,46),(99,40),(99,41),(130,38),(130,39)]
  lowerOrder := 59
  orderCap := 79
  rank := 16
  parentStrip := 37

theorem band148_checked : band148.check rectangle=true := by decide +kernel
#print axioms band148_checked

def band149 : Band CellKey where
  qlo := (581/1216)
  qhi := (23/48)
  mlo := (22956521739130434782608695652173/1000000000000000000000000000000)
  mhi := (2771739130434782608695652173913/62500000000000000000000000000)
  cells := [(80,41),(99,40),(99,41),(130,38),(130,39)]
  lowerOrder := 80
  orderCap := 98
  rank := 22
  parentStrip := 37

theorem band149_checked : band149.check rectangle=true := by decide +kernel
#print axioms band149_checked

def band150 : Band CellKey where
  qlo := (581/1216)
  qhi := (23/48)
  mlo := (13565217391304347826086956521739/500000000000000000000000000000)
  mhi := (2771739130434782608695652173913/62500000000000000000000000000)
  cells := [(99,40),(99,41),(130,38),(130,39)]
  lowerOrder := 99
  orderCap := 129
  rank := 26
  parentStrip := 37

theorem band150_checked : band150.check rectangle=true := by decide +kernel
#print axioms band150_checked

def band151 : Band CellKey where
  qlo := (581/1216)
  qhi := (23/48)
  mlo := (1721739130434782608695652173913/50000000000000000000000000000)
  mhi := (2771739130434782608695652173913/62500000000000000000000000000)
  cells := [(130,38),(130,39)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 37

theorem band151_checked : band151.check rectangle=true := by decide +kernel
#print axioms band151_checked

def band152 : Band CellKey where
  qlo := (23/48)
  qhi := (2983/6208)
  mlo := (1105598390881662755615152531009/62500000000000000000000000000)
  mhi := (22111967817633255112303050620181/500000000000000000000000000000)
  cells := [(59,47),(99,42),(99,43),(130,40)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 38

theorem band152_checked : band152.check rectangle=true := by decide +kernel
#print axioms band152_checked

def band153 : Band CellKey where
  qlo := (23/48)
  qhi := (2983/6208)
  mlo := (4578478042239356352665102246061/200000000000000000000000000000)
  mhi := (22111967817633255112303050620181/500000000000000000000000000000)
  cells := [(80,42),(99,42),(99,43),(130,40)]
  lowerOrder := 80
  orderCap := 98
  rank := 22
  parentStrip := 38

theorem band153_checked : band153.check rectangle=true := by decide +kernel
#print axioms band153_checked

def band154 : Band CellKey where
  qlo := (23/48)
  qhi := (2983/6208)
  mlo := (27054642976868923902111967817633/1000000000000000000000000000000)
  mhi := (22111967817633255112303050620181/500000000000000000000000000000)
  cells := [(99,42),(99,43),(130,40)]
  lowerOrder := 99
  orderCap := 129
  rank := 26
  parentStrip := 38

theorem band154_checked : band154.check rectangle=true := by decide +kernel
#print axioms band154_checked

def band155 : Band CellKey where
  qlo := (23/48)
  qhi := (2983/6208)
  mlo := (34338585316795172644988266845457/1000000000000000000000000000000)
  mhi := (22111967817633255112303050620181/500000000000000000000000000000)
  cells := [(130,40)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 38

theorem band155_checked : band155.check rectangle=true := by decide +kernel
#print axioms band155_checked

def band156 : Band CellKey where
  qlo := (2983/6208)
  qhi := (4487/9312)
  mlo := (8820147091597949632271005125919/500000000000000000000000000000)
  mhi := (11025183864497437040338756407399/250000000000000000000000000000)
  cells := [(59,48),(59,49),(99,44),(130,41),(130,42)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 39

theorem band156_checked : band156.check rectangle=true := by decide +kernel
#print axioms band156_checked

def band157 : Band CellKey where
  qlo := (2983/6208)
  qhi := (4487/9312)
  mlo := (456572320035658569199910853577/20000000000000000000000000000)
  mhi := (11025183864497437040338756407399/250000000000000000000000000000)
  cells := [(80,43),(99,44),(130,41),(130,42)]
  lowerOrder := 80
  orderCap := 98
  rank := 22
  parentStrip := 39

theorem band157_checked : band157.check rectangle=true := by decide +kernel
#print axioms band157_checked

def band158 : Band CellKey where
  qlo := (2983/6208)
  qhi := (4487/9312)
  mlo := (28016937820369957655449075105861/1000000000000000000000000000000)
  mhi := (11025183864497437040338756407399/250000000000000000000000000000)
  cells := [(99,44),(130,41),(130,42)]
  lowerOrder := 99
  orderCap := 129
  rank := 27
  parentStrip := 39

theorem band158_checked : band158.check rectangle=true := by decide +kernel
#print axioms band158_checked

def band159 : Band CellKey where
  qlo := (2983/6208)
  qhi := (4487/9312)
  mlo := (1369716960106975707599732560731/40000000000000000000000000000)
  mhi := (11025183864497437040338756407399/250000000000000000000000000000)
  cells := [(130,41),(130,42)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 39

theorem band159_checked : band159.check rectangle=true := by decide +kernel
#print axioms band159_checked

end ForestUnimodality.IntermediateBridgeCoverData

