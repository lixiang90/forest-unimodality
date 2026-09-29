import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell225
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 47
  A := (-21557282450906808445978413/50000000000000000000000000)
  B := (5844711496766431813032483/100000000000000000000000000)
  C := (14264619606414857821974351/100000000000000000000000000)
  dδ := (39448917401883887290381381/1000000000000000000000000000)
  dM := (16388554709080203029836209/25000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(21346857513392132332796791/5000000000000000000000000), (739801338252812357154653/50000000000000000000000), (11303763644377312624911269/100000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (653/1128)
  hi := (7/12)
  vmin := (35/144)
  damping := (35/144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell225
