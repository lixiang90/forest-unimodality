import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band224 : Band CellKey where
  qlo := (203/404)
  qhi := (407/808)
  mlo := (4218673218673218673218673218673/250000000000000000000000000000)
  mhi := (23377887028874911978502957975793/500000000000000000000000000000)
  cells := [(59,102),(59,103),(59,104),(99,64),(99,65),(130,72)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 56

theorem band224_checked : band224.check rectangle=true := by decide +kernel
#print axioms band224_checked

def band225 : Band CellKey where
  qlo := (203/404)
  qhi := (407/808)
  mlo := (11415233415233415233415233415233/500000000000000000000000000000)
  mhi := (23377887028874911978502957975793/500000000000000000000000000000)
  cells := [(80,89),(99,64),(99,65),(130,72)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 56

theorem band225_checked : band225.check rectangle=true := by decide +kernel
#print axioms band225_checked

def band226 : Band CellKey where
  qlo := (203/404)
  qhi := (407/808)
  mlo := (27793611793611793611793611793611/1000000000000000000000000000000)
  mhi := (23377887028874911978502957975793/500000000000000000000000000000)
  cells := [(99,64),(99,65),(130,72)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 56

theorem band226_checked : band226.check rectangle=true := by decide +kernel
#print axioms band226_checked

def band227 : Band CellKey where
  qlo := (203/404)
  qhi := (407/808)
  mlo := (4590909090909090909090909090909/125000000000000000000000000000)
  mhi := (23377887028874911978502957975793/500000000000000000000000000000)
  cells := [(130,72)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 56

theorem band227_checked : band227.check rectangle=true := by decide +kernel
#print axioms band227_checked

def band228 : Band CellKey where
  qlo := (407/808)
  qhi := (51/101)
  mlo := (16833333333333333333333333333333/1000000000000000000000000000000)
  mhi := (23349290559525940069927659232053/500000000000000000000000000000)
  cells := [(59,105),(59,106),(59,107),(99,66),(99,67),(130,73),(130,74)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 57

theorem band228_checked : band228.check rectangle=true := by decide +kernel
#print axioms band228_checked

def band229 : Band CellKey where
  qlo := (407/808)
  qhi := (51/101)
  mlo := (5693627450980392156862745098039/250000000000000000000000000000)
  mhi := (23349290559525940069927659232053/500000000000000000000000000000)
  cells := [(80,90),(99,66),(99,67),(130,73),(130,74)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 57

theorem band229_checked : band229.check rectangle=true := by decide +kernel
#print axioms band229_checked

def band230 : Band CellKey where
  qlo := (407/808)
  qhi := (51/101)
  mlo := (27725490196078431372549019607843/1000000000000000000000000000000)
  mhi := (23349290559525940069927659232053/500000000000000000000000000000)
  cells := [(99,66),(99,67),(130,73),(130,74)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 57

theorem band230_checked : band230.check rectangle=true := by decide +kernel
#print axioms band230_checked

def band231 : Band CellKey where
  qlo := (407/808)
  qhi := (51/101)
  mlo := (18318627450980392156862745098039/500000000000000000000000000000)
  mhi := (23349290559525940069927659232053/500000000000000000000000000000)
  cells := [(130,73),(130,74)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 57

theorem band231_checked : band231.check rectangle=true := by decide +kernel
#print axioms band231_checked

def band232 : Band CellKey where
  qlo := (51/101)
  qhi := (10429/20604)
  mlo := (3358596222073065490459296193307/200000000000000000000000000000)
  mhi := (46643833695481616544696695004233/1000000000000000000000000000000)
  cells := [(59,108),(59,109),(99,68),(99,69),(130,75)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 58

theorem band232_checked : band232.check rectangle=true := by decide +kernel
#print axioms band232_checked

def band233 : Band CellKey where
  qlo := (51/101)
  qhi := (10429/20604)
  mlo := (22719915619906031258989356601783/1000000000000000000000000000000)
  mhi := (46643833695481616544696695004233/1000000000000000000000000000000)
  cells := [(80,91),(99,68),(99,69),(130,75)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 58

theorem band233_checked : band233.check rectangle=true := by decide +kernel
#print axioms band233_checked

def band234 : Band CellKey where
  qlo := (51/101)
  qhi := (10429/20604)
  mlo := (27659027711189951097900086297823/1000000000000000000000000000000)
  mhi := (46643833695481616544696695004233/1000000000000000000000000000000)
  cells := [(99,68),(99,69),(130,75)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 58

theorem band234_checked : band234.check rectangle=true := by decide +kernel
#print axioms band234_checked

def band235 : Band CellKey where
  qlo := (51/101)
  qhi := (10429/20604)
  mlo := (7309885895100201361587879950139/200000000000000000000000000000)
  mhi := (46643833695481616544696695004233/1000000000000000000000000000000)
  cells := [(130,75)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 58

theorem band235_checked : band235.check rectangle=true := by decide +kernel
#print axioms band235_checked

def band236 : Band CellKey where
  qlo := (10429/20604)
  qhi := (5227/10302)
  mlo := (16752821886359288310694471015879/1000000000000000000000000000000)
  mhi := (46588161457329241332401016155093/1000000000000000000000000000000)
  cells := [(59,110),(59,111),(99,70),(99,71),(130,76)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 59

theorem band236_checked : band236.check rectangle=true := by decide +kernel
#print axioms band236_checked

def band237 : Band CellKey where
  qlo := (10429/20604)
  qhi := (5227/10302)
  mlo := (11332791276066577386646259804859/500000000000000000000000000000)
  mhi := (46588161457329241332401016155093/1000000000000000000000000000000)
  cells := [(80,92),(99,70),(99,71),(130,76)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 59

theorem band237_checked : band237.check rectangle=true := by decide +kernel
#print axioms band237_checked

def band238 : Band CellKey where
  qlo := (10429/20604)
  qhi := (5227/10302)
  mlo := (13796441553472355079395446718959/500000000000000000000000000000)
  mhi := (46588161457329241332401016155093/1000000000000000000000000000000)
  cells := [(99,70),(99,71),(130,76)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 59

theorem band238_checked : band238.check rectangle=true := by decide +kernel
#print axioms band238_checked

def band239 : Band CellKey where
  qlo := (10429/20604)
  qhi := (5227/10302)
  mlo := (18231012052802754926343983164339/500000000000000000000000000000)
  mhi := (46588161457329241332401016155093/1000000000000000000000000000000)
  cells := [(130,76)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 59

theorem band239_checked : band239.check rectangle=true := by decide +kernel
#print axioms band239_checked

end ForestUnimodality.IntermediateBridgeCoverData

