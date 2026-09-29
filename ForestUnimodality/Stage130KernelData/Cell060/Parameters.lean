import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 73
  A := (-8229652952652127489940881/5000000000000000000000000)
  B := (11599349062781302843738729/100000000000000000000000000)
  C := (-10245027328345001661757951/10000000000000000000000000000)
  dδ := (35871268068160079567352483/500000000000000000000000000)
  dM := (1422897736806617895524707/1000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(10933984097677209579302371/5000000000000000000000000), (257383727207094237243723/25000000000000000000000), (29400607734123429537476113/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3193/6468)
  hi := (49/99)
  vmin := (10457075/41835024)
  damping := (10457075/41835024)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell060
