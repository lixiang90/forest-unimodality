import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell176
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 91
  A := (-42282921347493089946567579/100000000000000000000000000)
  B := (107775387157295399198631/800000000000000000000000)
  C := (68311158526714010896796481/100000000000000000000000000)
  dδ := (8371509161021918610234849/50000000000000000000000000)
  dM := (26294598808065069474315667/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(93707157783043371068742999/10000000000000000000000000), (2915045797570313901303507/125000000000000000000000), (42794606725759756216120877/5000000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (57/107)
  hi := (29/54)
  vmin := (725/2916)
  damping := (725/2916)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell176
