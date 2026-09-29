import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band256 : Band CellKey where
  qlo := (5381/10506)
  qhi := (10787/21012)
  mlo := (3311430425512190599796050801891/200000000000000000000000000000)
  mhi := (46317005609183463468427705346243/1000000000000000000000000000000)
  cells := [(59,120),(59,121),(99,80),(99,81),(130,85),(130,86)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 64

theorem band256_checked : band256.check rectangle=true := by decide +kernel
#print axioms band256_checked

def band257 : Band CellKey where
  qlo := (5381/10506)
  qhi := (10787/21012)
  mlo := (22400852878464818763326226012793/1000000000000000000000000000000)
  mhi := (46317005609183463468427705346243/1000000000000000000000000000000)
  cells := [(80,97),(99,80),(99,81),(130,85),(130,86)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 64

theorem band257_checked : band257.check rectangle=true := by decide +kernel
#print axioms band257_checked

def band258 : Band CellKey where
  qlo := (5381/10506)
  qhi := (10787/21012)
  mlo := (13635301752109020116807268007787/500000000000000000000000000000)
  mhi := (46317005609183463468427705346243/1000000000000000000000000000000)
  cells := [(99,80),(99,81),(130,85),(130,86)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 64

theorem band258_checked : band258.check rectangle=true := by decide +kernel
#print axioms band258_checked

def band259 : Band CellKey where
  qlo := (5381/10506)
  qhi := (10787/21012)
  mlo := (1801807731528691944006674701029/50000000000000000000000000000)
  mhi := (46317005609183463468427705346243/1000000000000000000000000000000)
  cells := [(130,85),(130,86)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 64

theorem band259_checked : band259.check rectangle=true := by decide +kernel
#print axioms band259_checked

def band260 : Band CellKey where
  qlo := (10787/21012)
  qhi := (53/103)
  mlo := (4129716981132075471698113207547/250000000000000000000000000000)
  mhi := (23131775359722551964075224162969/500000000000000000000000000000)
  cells := [(59,122),(59,123),(99,82),(99,83),(130,87),(130,88)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 65

theorem band260_checked : band260.check rectangle=true := by decide +kernel
#print axioms band260_checked

def band261 : Band CellKey where
  qlo := (10787/21012)
  qhi := (53/103)
  mlo := (2234905660377358490566037735849/100000000000000000000000000000)
  mhi := (23131775359722551964075224162969/500000000000000000000000000000)
  cells := [(80,98),(99,82),(99,83),(130,87),(130,88)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 65

theorem band261_checked : band261.check rectangle=true := by decide +kernel
#print axioms band261_checked

def band262 : Band CellKey where
  qlo := (10787/21012)
  qhi := (53/103)
  mlo := (1088301886792452830188679245283/40000000000000000000000000000)
  mhi := (23131775359722551964075224162969/500000000000000000000000000000)
  cells := [(99,82),(99,83),(130,87),(130,88)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 65

theorem band262_checked : band262.check rectangle=true := by decide +kernel
#print axioms band262_checked

def band263 : Band CellKey where
  qlo := (10787/21012)
  qhi := (53/103)
  mlo := (2247051886792452830188679245283/62500000000000000000000000000)
  mhi := (23131775359722551964075224162969/500000000000000000000000000000)
  cells := [(130,87),(130,88)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 65

theorem band263_checked : band263.check rectangle=true := by decide +kernel
#print axioms band263_checked

def band264 : Band CellKey where
  qlo := (53/103)
  qhi := (21967/42642)
  mlo := (16500068284244548641143533482041/1000000000000000000000000000000)
  mhi := (23132208915103318395206659012793/500000000000000000000000000000)
  cells := [(59,124),(59,125),(99,84),(99,85),(130,89),(130,90)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 66

theorem band264_checked : band264.check rectangle=true := by decide +kernel
#print axioms band264_checked

def band265 : Band CellKey where
  qlo := (53/103)
  qhi := (21967/42642)
  mlo := (22323621796330859926253015887467/1000000000000000000000000000000)
  mhi := (23132208915103318395206659012793/500000000000000000000000000000)
  cells := [(80,99),(99,84),(99,85),(130,89),(130,90)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 66

theorem band265_checked : band265.check rectangle=true := by decide +kernel
#print axioms band265_checked

def band266 : Band CellKey where
  qlo := (53/103)
  qhi := (21967/42642)
  mlo := (424634110256293531205899758729/15625000000000000000000000000)
  mhi := (23132208915103318395206659012793/500000000000000000000000000000)
  cells := [(99,84),(99,85),(130,89),(130,90)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 66

theorem band266_checked : band266.check rectangle=true := by decide +kernel
#print axioms band266_checked

def band267 : Band CellKey where
  qlo := (53/103)
  qhi := (21967/42642)
  mlo := (7182382664906450584968361633359/200000000000000000000000000000)
  mhi := (23132208915103318395206659012793/500000000000000000000000000000)
  cells := [(130,89),(130,90)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 66

theorem band267_checked : band267.check rectangle=true := by decide +kernel
#print axioms band267_checked

def band268 : Band CellKey where
  qlo := (21967/42642)
  qhi := (10996/21321)
  mlo := (16481311385958530374681702437249/1000000000000000000000000000000)
  mhi := (46238144133404151746837099864629/1000000000000000000000000000000)
  cells := [(59,126),(59,127),(99,86),(99,87),(130,91),(130,92)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 67

theorem band268_checked : band268.check rectangle=true := by decide +kernel
#print axioms band268_checked

def band269 : Band CellKey where
  qlo := (21967/42642)
  qhi := (10996/21321)
  mlo := (2787280602037104401600582029829/125000000000000000000000000000)
  mhi := (46238144133404151746837099864629/1000000000000000000000000000000)
  cells := [(80,100),(99,86),(99,87),(130,91),(130,92)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 67

theorem band269_checked : band269.check rectangle=true := by decide +kernel
#print axioms band269_checked

def band270 : Band CellKey where
  qlo := (21967/42642)
  qhi := (10996/21321)
  mlo := (27145689341578755911240451073117/1000000000000000000000000000000)
  mhi := (46238144133404151746837099864629/1000000000000000000000000000000)
  cells := [(99,86),(99,87),(130,91),(130,92)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 67

theorem band270_checked : band270.check rectangle=true := by decide +kernel
#print axioms band270_checked

def band271 : Band CellKey where
  qlo := (21967/42642)
  qhi := (10996/21321)
  mlo := (3587108948708621316842488177519/100000000000000000000000000000)
  mhi := (46238144133404151746837099864629/1000000000000000000000000000000)
  cells := [(130,91),(130,92)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 67

theorem band271_checked : band271.check rectangle=true := by decide +kernel
#print axioms band271_checked

end ForestUnimodality.IntermediateBridgeCoverData

