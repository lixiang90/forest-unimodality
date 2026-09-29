import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 42
  A := (-17391739848648193389024641/50000000000000000000000000)
  B := (94824582878806684682615469/1000000000000000000000000000)
  C := (57390480307478860741432491/10000000000000000000000000000)
  dδ := (2799543177531187837514537/25000000000000000000000000)
  dM := (19315577242996350045001197/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(26102765402826055840534991/5000000000000000000000000), (11449180758537833568766473/5000000000000000000000000), (34035543291683538313918689/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
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
end ForestUnimodality.Stage80KernelData.Cell130
