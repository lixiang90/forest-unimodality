import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (-14509641682055135767370757/250000000000000000000000000)
  B := (41768767590188167482256887/500000000000000000000000000)
  C := (980642276536489556140741/500000000000000000000000000)
  dδ := (5896919179052061837920107/50000000000000000000000000)
  dM := (3799023617462852012161001/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(57949682742221186870779093/10000000000000000000000000), (5561264800671241737006767/2500000000000000000000000), (30806520139854892903485961/1000000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (10429/20604)
  hi := (5227/10302)
  vmin := (26527025/106131204)
  damping := (26527025/106131204)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell092
