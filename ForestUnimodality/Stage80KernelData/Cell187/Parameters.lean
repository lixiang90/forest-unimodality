import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell187
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 76
  A := (-5156084268713980406317887/5000000000000000000000000)
  B := (9511033731463799933969483/50000000000000000000000000)
  C := (13085473771209630289291681/20000000000000000000000000)
  dδ := (17688862938450689021863127/100000000000000000000000000)
  dM := (4863325277394754024909429/1250000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(45863805084791176014391567/5000000000000000000000000), (5977539001660046480424171/250000000000000000000000)]
  retention := ![(3/5), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2567/4752)
  hi := (643/1188)
  vmin := (350435/1411344)
  damping := (350435/1411344)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell187
