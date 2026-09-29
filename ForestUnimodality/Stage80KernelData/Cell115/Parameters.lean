import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 36
  A := (-2348826985919035625727247/20000000000000000000000000)
  B := (10039857721730764683609749/100000000000000000000000000)
  C := (72490885766774235815512739/10000000000000000000000000000)
  dδ := (13158251716556784716161133/100000000000000000000000000)
  dM := (4931545573781932409462847/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(27715134430096730611126077/5000000000000000000000000), (51284874998540468382657309/10000000000000000000000000), (25086720836241759968743281/1000000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11311/21736)
  hi := (22647/43472)
  vmin := (471623775/1889814784)
  damping := (471623775/1889814784)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell115
