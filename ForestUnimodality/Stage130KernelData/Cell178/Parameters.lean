import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell178
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 68
  A := (-2353664402881120916433133/1250000000000000000000000)
  B := (26174449805739275235969/195312500000000000000000)
  C := (2991383389132532856502511/500000000000000000000000000)
  dδ := (75711941571975985287856759/1000000000000000000000000000)
  dM := (4314356694041977411877009/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(15535916901066419981702893/1000000000000000000000000), (50511432401834966299247753/1000000000000000000000000)]
  retention := ![(3/5), (1/100)]
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
end ForestUnimodality.Stage130KernelData.Cell178
