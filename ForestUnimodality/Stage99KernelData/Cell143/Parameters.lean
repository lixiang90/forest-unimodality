import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 117
  A := (10992567267577342150275399/100000000000000000000000000)
  B := (91897160959376111843965873/1000000000000000000000000000)
  C := (13264197417746317331221917/20000000000000000000000000)
  dδ := (722356266138936276011151/5000000000000000000000000)
  dM := (15806190767805672683921081/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(12755610041450756497738439/2000000000000000000000000), (41720953537315335069024513/10000000000000000000000000), (22137985717059269319406667/1000000000000000000000000), (21641109089518582919708933/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (47837/90312)
  hi := (95699/180624)
  vmin := (8127237575/32625029376)
  damping := (8127237575/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell143
