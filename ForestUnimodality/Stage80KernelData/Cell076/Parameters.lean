import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (13890678853050937957647193/10000000000000000000000000)
  B := (18056328025935590442241363/2500000000000000000000000000)
  C := (-2685168157416836440254393/2000000000000000000000000000)
  dδ := (10324419890665867405310507/100000000000000000000000000)
  dM := (599495464411395599673869/781250000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(552991706803072702314239/100000000000000000000000), (30180370141857695287512797/5000000000000000000000000), (1436059258703741825513589/50000000000000000000000)]
  retention := ![(4/5), (3/20), (1/10)]
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
end ForestUnimodality.Stage80KernelData.Cell076
