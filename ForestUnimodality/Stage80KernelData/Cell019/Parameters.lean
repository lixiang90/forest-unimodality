import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 32
  A := (-78191646287138417683593161/1000000000000000000000000000)
  B := (14695100871660669861196169/250000000000000000000000000)
  C := (-918308145997402333615689/6250000000000000000000000)
  dδ := (1260801967821183894313819/25000000000000000000000000)
  dM := (92006060341833482713741477/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(6026832461726788769951213/5000000000000000000000000), (11444580675373599021327209/1000000000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (101/255)
  hi := (103/255)
  vmin := (15554/65025)
  damping := (15554/65025)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell019
