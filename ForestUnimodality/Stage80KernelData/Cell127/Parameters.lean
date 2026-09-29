import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 33
  A := (2738604424388922858213391/3125000000000000000000000)
  B := (51040459876439660258373721/1000000000000000000000000000)
  C := (85452217884481335846702521/10000000000000000000000000000)
  dδ := (16348800575911465182699089/100000000000000000000000000)
  dM := (10262850699507585546660371/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(68787563716246635792117559/10000000000000000000000000), (18078336513200813584489879/1000000000000000000000000), (87643277470083091884589521/10000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11/21)
  hi := (1549/2954)
  vmin := (2176345/8726116)
  damping := (2176345/8726116)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell127
