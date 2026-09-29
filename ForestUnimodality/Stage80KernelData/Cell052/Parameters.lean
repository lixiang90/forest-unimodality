import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 35
  A := (16950670612338685544528971/5000000000000000000000000)
  B := (-5047890778151704720133619/62500000000000000000000000)
  C := (-39234055333985107250072133/10000000000000000000000000000)
  dδ := (14747780949797412164414823/100000000000000000000000000)
  dM := 0
  wL := 0
  wR := 0
  wC := 1
  price := ![(75882891496221818172784879/10000000000000000000000000), (23059230260146843960455953/1000000000000000000000000), (37995351543688582474089799/5000000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9237/19012)
  hi := (4631/9506)
  vmin := (90291675/361456144)
  damping := (90291675/361456144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell052
