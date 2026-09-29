import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell189
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 72
  A := (-24365769046578826278803831/25000000000000000000000000)
  B := (9297009442785665600528233/50000000000000000000000000)
  C := (24375875535010429161209/39062500000000000000000)
  dδ := (8584655658249196186204699/50000000000000000000000000)
  dM := (4795949618685573672717537/1250000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(41779720149095087577961749/5000000000000000000000000), (11414132568001015499703499/500000000000000000000000)]
  retention := ![(3/5), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (859/1584)
  hi := (1291/2376)
  vmin := (1400735/5645376)
  damping := (1400735/5645376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell189
