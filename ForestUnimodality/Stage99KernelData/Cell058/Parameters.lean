import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 57
  A := (7816860309702947851207/20000000000000000000000)
  B := (41626273331318457138205957/1000000000000000000000000000)
  C := (-1110359417170333432706153/10000000000000000000000000000)
  dδ := (1045925708272129293907593/12500000000000000000000000)
  dM := (16305651059125268482336013/20000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(27629747378087756715103751/5000000000000000000000000), (37307415914395756217913913/10000000000000000000000000), (24025299463797495036487817/500000000000000000000000)]
  retention := ![(4/5), (1/2), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (197/396)
  hi := (395/792)
  vmin := (39203/156816)
  damping := (39203/156816)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell058
