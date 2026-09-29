import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 107
  A := (32021203998742870822979967/100000000000000000000000000)
  B := (37891227437474278572082653/500000000000000000000000000)
  C := (7368859659599129308116261/12500000000000000000000000)
  dδ := (203885231906854270597651/1562500000000000000000000)
  dM := (6602115036502491764516809/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(14686689119511221690572711/2000000000000000000000000), (34680075097875011636006093/10000000000000000000000000), (43528512060444972675554709/5000000000000000000000000), (7524460899642504863038539/250000000000000000000000)]
  retention := ![(4/5), (3/5), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (97103/182328)
  hi := (57/107)
  vmin := (2850/11449)
  damping := (2850/11449)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell155
