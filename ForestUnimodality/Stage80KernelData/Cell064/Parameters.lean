import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 38
  A := (1660323401299760147651341/1000000000000000000000000)
  B := (-9835779055558419199656317/1250000000000000000000000000)
  C := (-4100304990682238429067219/2000000000000000000000000000)
  dδ := (2522030862426180575219803/25000000000000000000000000)
  dM := (27734129543259409189301379/50000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(59317904215207777340879147/10000000000000000000000000), (2710094625845746563186367/250000000000000000000000), (11394666697197958882270541/500000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9287/19012)
  hi := (24/49)
  vmin := (90316075/361456144)
  damping := (90316075/361456144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell064
