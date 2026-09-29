import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 91
  A := (-3288923122734136097449209/2000000000000000000000000)
  B := (98817883928946387284142361/1000000000000000000000000000)
  C := (17088384746015282834169513/10000000000000000000000000000)
  dδ := (15149676751007389030601047/250000000000000000000000000)
  dM := (10389023875702423603539781/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(2198860001505959260725831/200000000000000000000000), (3047476128252054827783013/2000000000000000000000000), (19194655124611916363619457/250000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (5381/10506)
  hi := (10787/21012)
  vmin := (110297075/441504144)
  damping := (110297075/441504144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell086
