import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 69
  A := (-2446016173506274296016727/2000000000000000000000000)
  B := (5135317039292174035036709/50000000000000000000000000)
  C := (-11926732497861110629533421/5000000000000000000000000000)
  dδ := (19359215824749195083986919/250000000000000000000000000)
  dM := (3352890082867873884631127/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(54587508894701750605804591/10000000000000000000000000), (12057322943389152669624309/2500000000000000000000000), (7177533791202701962674837/125000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4631/9506)
  hi := (9287/19012)
  vmin := (22576125/90364036)
  damping := (22576125/90364036)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell051
