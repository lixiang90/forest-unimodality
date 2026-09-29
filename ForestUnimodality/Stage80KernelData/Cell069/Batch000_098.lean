import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell069.Parameters
import ForestUnimodality.BinomialMassData.Q9529_19404.Batch000_049
import ForestUnimodality.BinomialMassData.Q9529_19404.Batch050_099
import ForestUnimodality.BinomialMassData.Q4777_9702.Batch000_049
import ForestUnimodality.BinomialMassData.Q4777_9702.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree000.table
  base := (189427685981602362491571511/5000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (581866734882007727303054900000000000000)
      linear := (9502716484410742014965478500000000000)
      constant := (189427685981602362491571511000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree000.table
  base := (189427685981602362491571511/5000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (581866734882007727303054900000000000000)
      linear := (9502716484410742014965478500000000000)
      constant := (189427685981602362491571511000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree001.table
  base := (223855071180887284719559289520904949280987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-26449654305352017178656274703080743000000000000)
      constant := (5274187218855701026162233451192396255124991562387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree001.table
  base := (223448073780802053524954655794740240973421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-26520220193624832665784952686078243000000000000)
      constant := (5264643797268515104332521050462259023874978629621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24996025209852469769/50000000000000000000)
  directionHi := (49992050419704939539/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree002.table
  base := (135487546665076946002481582029422571423381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-53346548279418368252623174702407843000000000000)
      constant := (3214298201720964846245050162113912163171857791581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree002.table
  base := (13502357924650977704474640593647740045053/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-26743840027981999613440265334201421500000000000)
      constant := (1601758835882060682168089590522067690179681258265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24996025209852469769/50000000000000000000)
  centralHi := (49992050419704939539/100000000000000000000)
  directionLo := (8837429464298288003/12500000000000000000)
  directionHi := (2827977428575452161/4000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree003.table
  base := (84454315185283466422435356898964696835381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3042801102323803804988594626852200000000000000)
      linear := (-8915938028164968814065563855748327000000000000)
      constant := (227352879465407104420334899638225441453805511509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree003.table
  base := (84052198533723141893563822215095489879077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3042801102323803804988594626852200000000000000)
      linear := (-8939459990922573976441789850080827000000000000)
      constant := (226335976665266529115704226112012154836433962053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8837429464298288003/12500000000000000000)
  centralHi := (2827977428575452161/4000000000000000000)
  directionLo := (86588771301473971569/100000000000000000000)
  directionHi := (8658877130147397157/10000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree004.table
  base := (850196129728548038977463205687525334087/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-53570168113775535200278487350531021500000000000)
      constant := (692618864827683654680130705964569807838477935584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree004.table
  base := (54096398324278712658218159801309777444859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-107422599780642332349071686633052043000000000000)
      constant := (1378350813951128384454322018093742068097688404659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86588771301473971569/100000000000000000000)
  centralHi := (8658877130147397157/10000000000000000000)
  directionLo := (24996025209852469769/25000000000000000000)
  directionHi := (99984100839409879077/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree005.table
  base := (36244247495874573998293025322392478781363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-134037230201617421474523874700389143000000000000)
      constant := (1016916788815300613642241597241143295321269169963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree005.table
  base := (36004310263441432054136037514961282568149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-134390059642981498910167264615376643000000000000)
      constant := (1012135138006145561808036125119915061111478465949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24996025209852469769/25000000000000000000)
  centralHi := (99984100839409879077/100000000000000000000)
  directionLo := (111785623073057136791/100000000000000000000)
  directionHi := (13973202884132142099/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree006.table
  base := (24844162037153762110357831726247729262853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3042801102323803804988594626852200000000000000)
      linear := (-17881569352853752505387863855524027000000000000)
      constant := (91230620974576763719852883626345348478559847717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree006.table
  base := (24662303763576189151215495797617580530569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3042801102323803804988594626852200000000000000)
      linear := (-17928613278368962830140315844189027000000000000)
      constant := (90893531036052527670891565918191701019892928041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111785623073057136791/100000000000000000000)
  centralHi := (13973202884132142099/12500000000000000000)
  directionLo := (122455014723766723037/100000000000000000000)
  directionHi := (61227507361883361519/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree007.table
  base := (433902704073458227476330794933821341181/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (18249462)
      previous := (9124731)
      next := (9124731)
      square := (279440917560349329029564812670100000000000000)
      linear := (-1916643042344389016555690558153503500000000000)
      constant := (7454099438550984688520117126746345430616681380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree007.table
  base := (17215304668382678792134306945814616104551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (36498924)
      previous := (18249462)
      next := (18249462)
      square := (558881835120698658059129625340200000000000000)
      linear := (-3843366925870608816986906542449507000000000000)
      constant := (14875195081431545894302910988560985069594513199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122455014723766723037/100000000000000000000)
  centralHi := (61227507361883361519/50000000000000000000)
  directionLo := (16533316617592682509/12500000000000000000)
  directionHi := (132266532940741460073/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree008.table
  base := (12175358416047742577156840324037739097991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-214727912123816474696424574698370443000000000000)
      constant := (707432488363126310208001174092795802039482908191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree008.table
  base := (12062397039406041686179830231572988161999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-215292439229998998593453998562350443000000000000)
      constant := (706990401355341182900724465795606347598781029799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16533316617592682509/12500000000000000000)
  centralHi := (132266532940741460073/100000000000000000000)
  directionLo := (8837429464298288003/6250000000000000000)
  directionHi := (141398871428772608049/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree009.table
  base := (8395650343956702047219085095695369382691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (22079596)
      previous := (11039798)
      next := (11039798)
      square := (338089011369311533887621625205800000000000000)
      linear := (-2983022297504726244078907095033303000000000000)
      constant := (9019030478209900947980021222568535158428772011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree009.table
  base := (830119284661574807938810940545671968003/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (11039798)
      previous := (5519899)
      next := (5519899)
      square := (169044505684655766943810812602900000000000000)
      linear := (-1495431475878630649102157879905401500000000000)
      constant := (4513111913070287586240180309352753079080997815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8837429464298288003/6250000000000000000)
  centralHi := (141398871428772608049/100000000000000000000)
  directionLo := (74988075629557409307/50000000000000000000)
  directionHi := (29995230251822963723/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree010.table
  base := (5501155516474230069981041018943338629003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-268521700071949176844358374697024643000000000000)
      constant := (787690107792854949723006796885489944728763025603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree010.table
  base := (5418975846239123166403664373825697480653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-269227358954677331715645154526999643000000000000)
      constant := (789220402971858385204135837383069257079920007253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74988075629557409307/50000000000000000000)
  centralHi := (29995230251822963723/20000000000000000000)
  directionLo := (158088744228244182147/100000000000000000000)
  directionHi := (39522186057061045537/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree011.table
  base := (798673378945183733788306146013495203157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 972405000000000000000000000000000000000000000
      center := (7390278)
      previous := (3695139)
      next := (3695139)
      square := (113162024466587744813625420006900000000000000)
      linear := (-1220737991925683999662501135108891500000000000)
      constant := (3602830976079713285757894684000060746210353034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree011.table
  base := (1560406397270075655887492422247755871523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 972405000000000000000000000000000000000000000
      center := (7390278)
      previous := (3695139)
      next := (3695139)
      square := (113162024466587744813625420006900000000000000)
      linear := (-1223945532301721067259259225245141500000000000)
      constant := (3612970215477597771602548271281503559649664563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158088744228244182147/100000000000000000000)
  centralHi := (39522186057061045537/25000000000000000000)
  directionLo := (165804873742690474133/100000000000000000000)
  directionHi := (82902436871345237067/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree012.table
  base := (1301893824099932936089157982251564226599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3042801102323803804988594626852200000000000000)
      linear := (-35812832002231319888032463855075427000000000000)
      constant := (108780345768613710206640324135275059216081912711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree012.table
  base := (616928067484938340977762024599577446881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1521400551161901902494297313426100000000000000)
      linear := (-17953459926630870268768683916202713500000000000)
      constant := (54578434110859917807045103417197231555007835009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165804873742690474133/100000000000000000000)
  centralHi := (82902436871345237067/50000000000000000000)
  directionLo := (86588771301473971569/50000000000000000000)
  directionHi := (173177542602947943139/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree013.table
  base := (-141154121477287730557796457952376425443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-174606190997074115033129537347502971500000000000)
      constant := (553315875820285482171959274614305268403813809957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree013.table
  base := (-34597183239901998021051544718678118269/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-175064869270847415699465944236986721500000000000)
      constant := (555495145583625301225280231701369838582960599655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86588771301473971569/50000000000000000000)
  centralHi := (173177542602947943139/100000000000000000000)
  directionLo := (18024890115382720601/10000000000000000000)
  directionHi := (180248901153827206011/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree014.table
  base := (-405893699083024278979691735358362931639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (18249462)
      previous := (9124731)
      next := (9124731)
      square := (279440917560349329029564812670100000000000000)
      linear := (-3837849754777699807553326272391153500000000000)
      constant := (12787406544770305538555501514126405870886603778) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree014.table
  base := (-420929144781661314274491195850580798363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (18249462)
      previous := (9124731)
      next := (9124731)
      square := (279440917560349329029564812670100000000000000)
      linear := (-3847930595959530591428851698533653500000000000)
      constant := (12842281230102068314501988812569420344333935226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18024890115382720601/10000000000000000000)
  centralHi := (180248901153827206011/100000000000000000000)
  directionLo := (187053124732864303733/100000000000000000000)
  directionHi := (93526562366432151867/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree015.table
  base := (-2764907829706754387264289761972931330643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3042801102323803804988594626852200000000000000)
      linear := (-44778463326920103579354763854851127000000000000)
      constant := (157512605511082239034895789793875694402012384973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree015.table
  base := (-141100399775389871216738624885031376929/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1521400551161901902494297313426100000000000000)
      linear := (-22448036570354064695617946913256813500000000000)
      constant := (79114913722039425297899160887606180690888899190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187053124732864303733/100000000000000000000)
  centralHi := (93526562366432151867/50000000000000000000)
  directionLo := (96809189359139368223/50000000000000000000)
  directionHi := (193618378718278736447/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree016.table
  base := (-747209897868813829760249538434966852451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-429903063916347283288159774692987243000000000000)
      constant := (1599274678113229929850180525887359260998928626745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree016.table
  base := (-3790372148897334715924637159209338515233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-431032118128712331082218622420947243000000000000)
      constant := (1606870137155637421784450370965939732982495482167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96809189359139368223/50000000000000000000)
  centralHi := (193618378718278736447/100000000000000000000)
  directionLo := (24996025209852469769/12500000000000000000)
  directionHi := (199968201678819758153/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree017.table
  base := (-4558783507902566936931251074733475311819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-456799957890413634362126674692314343000000000000)
      constant := (1797636907752508591100558890303860312283737616381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree017.table
  base := (-1152618340503401998722800101384566273839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-228999788995525748821657100201635921500000000000)
      constant := (903219410915024447595397762915342725542399220722) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24996025209852469769/12500000000000000000)
  centralHi := (199968201678819758153/100000000000000000000)
  directionLo := (103061252160823582199/50000000000000000000)
  directionHi := (206122504321647164399/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree018.table
  base := (-5249946011911873773503688852555443473591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (22079596)
      previous := (11039798)
      next := (11039798)
      square := (338089011369311533887621625205800000000000000)
      linear := (-5971566072400987474519673761625203000000000000)
      constant := (24843258609926167198323543074848506506608869089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree018.table
  base := (-1324771635720921371165309418295046473621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (11039798)
      previous := (5519899)
      next := (5519899)
      square := (169044505684655766943810812602900000000000000)
      linear := (-2993623690453028791385245545590101500000000000)
      constant := (12483825620447497485844620816158874106874306918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103061252160823582199/50000000000000000000)
  centralHi := (206122504321647164399/100000000000000000000)
  directionLo := (26512288392894864009/12500000000000000000)
  directionHi := (212098307143158912073/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree019.table
  base := (-1455788519884781465653603418103744692679/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-255296872919273168255030237345484271500000000000)
      constant := (1121477678623650512495982097206845993703389087042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree019.table
  base := (-5869801452471061863836247506862619855609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-511934497715729830765505356367921043000000000000)
      constant := (2254373126216439603893268647471360729671218034591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26512288392894864009/12500000000000000000)
  centralHi := (212098307143158912073/100000000000000000000)
  directionLo := (27238786969985493351/12500000000000000000)
  directionHi := (217910295759883946809/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree020.table
  base := (-3144907308859893019176367970824146288087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-268745319906306343792013687345147821500000000000)
      constant := (1244661353827779715722005600949960796395332810513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree020.table
  base := (-6334016597842953825353402593631603281133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-538901957578068997326600934350245643000000000000)
      constant := (2502150716982478265021362923548277401636118736267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27238786969985493351/12500000000000000000)
  centralHi := (217910295759883946809/100000000000000000000)
  directionLo := (223571246146114273583/100000000000000000000)
  directionHi := (13973202884132142099/6250000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree021.table
  base := (-6659727612931403546522955327051154363183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (4055436)
      previous := (2027718)
      next := (2027718)
      square := (62097981680077628673236625037800000000000000)
      linear := (-1279790326046891244122435997028623000000000000)
      constant := (6238492932828135581815607313147725102026191937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree021.table
  base := (-6701533446162878533109194662002962689187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (4055436)
      previous := (2027718)
      next := (2027718)
      square := (62097981680077628673236625037800000000000000)
      linear := (-1283150606440834838747611139076123000000000000)
      constant := (6270933951735201338601698897728380407942292493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223571246146114273583/100000000000000000000)
  centralHi := (13973202884132142099/6250000000000000000)
  directionLo := (229092355194346756381/100000000000000000000)
  directionHi := (114546177597173378191/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree022.table
  base := (-6941459250696693619198613250966199099263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1944810000000000000000000000000000000000000000
      center := (14780556)
      previous := (7390278)
      next := (7390278)
      square := (226324048933175489627250840013800000000000000)
      linear := (-4886648163311945369685629542883883000000000000)
      constant := (25027370274485308103264982152694006132976232497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree022.table
  base := (-3490462114734271255075090077938351986983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 972405000000000000000000000000000000000000000
      center := (7390278)
      previous := (3695139)
      next := (3695139)
      square := (113162024466587744813625420006900000000000000)
      linear := (-2449739162408046820036330951714441500000000000)
      constant := (12579193677385728224462333966634196867219559177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229092355194346756381/100000000000000000000)
  centralHi := (114546177597173378191/50000000000000000000)
  directionLo := (58620875288617886087/25000000000000000000)
  directionHi := (234483501154471544349/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree023.table
  base := (-892822890662823815369603210093575023349/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-309090660867405870402964037344138471500000000000)
      constant := (1660276871909525154676135486544647065092886555404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree023.table
  base := (-448735632942508959202571381508742261359/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-309902168582543248504943834148609721500000000000)
      constant := (1669010653391632825972688561836449101538043830728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58620875288617886087/25000000000000000000)
  centralHi := (234483501154471544349/100000000000000000000)
  directionLo := (47950690263571964097/20000000000000000000)
  directionHi := (119876725658929910243/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree024.table
  base := (-454365290592736447454836477976253355729/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1521400551161901902494297313426100000000000000)
      linear := (-35837678650493227326660831927089113500000000000)
      constant := (201541248377105067736123087941855483716498373752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree024.table
  base := (-7304824029285426064923607196703943951761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3042801102323803804988594626852200000000000000)
      linear := (-71863533003047295952331471808838227000000000000)
      constant := (405210252545711099059965976691846909492713982671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47950690263571964097/20000000000000000000)
  centralHi := (119876725658929910243/50000000000000000000)
  directionLo := (9796401177901337843/4000000000000000000)
  directionHi := (61227507361883361519/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree025.table
  base := (-732927970698352090255731045277036129581/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-335987554841472221476930937343465571500000000000)
      constant := (1974867973244893116758730831971503259947189311095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree025.table
  base := (-7362128362433606464674807831779095220757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-673739256889764830132078824261868643000000000000)
      constant := (3970635576720371506670096489868253406167006903843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9796401177901337843/4000000000000000000)
  centralHi := (61227507361883361519/25000000000000000000)
  directionLo := (24996025209852469769/10000000000000000000)
  directionHi := (249960252098524697691/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree026.table
  base := (-915788142902098968634812800481741474809/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-349436001828505397013914387343129121500000000000)
      constant := (2143203350314821963106458189742618091389032701564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree026.table
  base := (-7357105226175879521272939052598582134561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-700706716752103996693174402244193243000000000000)
      constant := (4309123624271346547299914806423223285894501501239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24996025209852469769/10000000000000000000)
  centralHi := (249960252098524697691/100000000000000000000)
  directionLo := (254910440614589855517/100000000000000000000)
  directionHi := (127455220307294927759/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree027.table
  base := (-7265791164091582350056166505454460642703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (22079596)
      previous := (11039798)
      next := (11039798)
      square := (338089011369311533887621625205800000000000000)
      linear := (-8960109847297248704960440428217103000000000000)
      constant := (57254816377075631703146501038168101889621281737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree027.table
  base := (-7294628704922530816024761524340785100187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (22079596)
      previous := (11039798)
      next := (11039798)
      square := (338089011369311533887621625205800000000000000)
      linear := (-8983631810054853867336666422549603000000000000)
      constant := (57558539723830755637807854385921734271908572573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254910440614589855517/100000000000000000000)
  centralHi := (127455220307294927759/50000000000000000000)
  directionLo := (64941578476105478677/25000000000000000000)
  directionHi := (259766313904421914709/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree028.table
  base := (-7152121492188369214122132175027788248259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (36498924)
      previous := (18249462)
      next := (18249462)
      square := (558881835120698658059129625340200000000000000)
      linear := (-15360526359288642779097195401732907000000000000)
      constant := (102108838073251856058498159855364550721561863509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree028.table
  base := (-717908507892734671087495454255709905209/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (18249462)
      previous := (9124731)
      next := (9124731)
      square := (279440917560349329029564812670100000000000000)
      linear := (-7700424862007982957299648553151453500000000000)
      constant := (51325373856822765847727752472592970868666414795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64941578476105478677/25000000000000000000)
  centralHi := (259766313904421914709/100000000000000000000)
  directionLo := (52906613176296584029/20000000000000000000)
  directionHi := (132266532940741460073/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree029.table
  base := (-1747311188307430934000904737206062716857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-389781342789604923624864737342119771500000000000)
      constant := (2691696298957055471324987427825403340331629975486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree029.table
  base := (-1402884867092502801907877202386091509849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-781609096339121496376461136191167043000000000000)
      constant := (5411965433391929544969976067164127659429199261755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52906613176296584029/20000000000000000000)
  centralHi := (132266532940741460073/50000000000000000000)
  directionLo := (67303857639172188009/25000000000000000000)
  directionHi := (269215430556688752037/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree030.table
  base := (-3390359610060426503426709810809098547567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1521400551161901902494297313426100000000000000)
      linear := (-44803309975182011017983131926864813500000000000)
      constant := (320985277195789887116107156141525867677760588337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree030.table
  base := (-3402102532917989002356884016894357085471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1521400551161901902494297313426100000000000000)
      linear := (-44920919788970036829864261898527313500000000000)
      constant := (322688575689680625600871436155729477866546916481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67303857639172188009/25000000000000000000)
  centralHi := (269215430556688752037/100000000000000000000)
  directionLo := (54763547421616004967/20000000000000000000)
  directionHi := (68454434277020006209/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree031.table
  base := (-261190090912798599578768996481388379977/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-833356473527342549397663274682893743000000000000)
      constant := (6186284763709802101805915917276319911332921515575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree031.table
  base := (-3275817041714591512441396687586509495081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-417772008031899914749326146077908121500000000000)
      constant := (3109548980829267281503118638806930726423345396719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54763547421616004967/20000000000000000000)
  centralHi := (68454434277020006209/25000000000000000000)
  directionLo := (55668791350326960539/20000000000000000000)
  directionHi := (34792994593954350337/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree032.table
  base := (-6239235486608390337380768296275971782647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-860253367501408900471630174682220843000000000000)
      constant := (6608973875340136439311613128198951056540422483953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree032.table
  base := (-1251920332622098304423213342523181067667/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-862511475926138996059747870138140843000000000000)
      constant := (6644008216595631897778675544357616655781327774665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55668791350326960539/20000000000000000000)
  centralHi := (34792994593954350337/12500000000000000000)
  directionLo := (8837429464298288003/3125000000000000000)
  directionHi := (282797742857545216097/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree033.table
  base := (-591177599757729653545276620999216046389/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 108045000000000000000000000000000000000000000
      center := (821142)
      previous := (410571)
      next := (410571)
      square := (12573558274065304979291713334100000000000000)
      linear := (-407323352376251263335903156419443500000000000)
      constant := (3234959124318039151987382680598547077267900495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree033.table
  base := (-5930713044932587040357077002599730066377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216090000000000000000000000000000000000000000
      center := (1642284)
      previous := (821142)
      next := (821142)
      square := (25147116548130609958583426668200000000000000)
      linear := (-816785065003193905069645039596387000000000000)
      constant := (6504190835806216956278723724765080932995659407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8837429464298288003/3125000000000000000)
  centralHi := (282797742857545216097/100000000000000000000)
  directionLo := (143591232732441386951/50000000000000000000)
  directionHi := (287182465464882773903/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree034.table
  base := (-693715579166731055370136335469129058021/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-457023577724770801309781987340437521500000000000)
      constant := (3748265367917846225224009216318363840096836663116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree034.table
  base := (-556731668779526173117928178110868795771/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-458223197825408664590969513051395021500000000000)
      constant := (3768104754021839759031875992173393044566444390145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143591232732441386951/50000000000000000000)
  centralHi := (287182465464882773903/100000000000000000000)
  directionLo := (7287531028049507897/2500000000000000000)
  directionHi := (291501241121980315881/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree035.table
  base := (-515520119486297719567768495251354929007/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (18249462)
      previous := (9124731)
      next := (9124731)
      square := (279440917560349329029564812670100000000000000)
      linear := (-9601469892077632180546233415104103500000000000)
      constant := (81237686540513148715428227884823235858496586285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree035.table
  base := (-5171529658669061194045243580367382428781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (36498924)
      previous := (18249462)
      next := (18249462)
      square := (558881835120698658059129625340200000000000000)
      linear := (-19253343990064418280470093960920707000000000000)
      constant := (163334601242903639095533113777695452455960353531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7287531028049507897/2500000000000000000)
  centralHi := (291501241121980315881/100000000000000000000)
  directionLo := (36969619850464133481/12500000000000000000)
  directionHi := (295756958803713067849/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree036.table
  base := (-4730117207388952107448312373427517842371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (22079596)
      previous := (11039798)
      next := (11039798)
      square := (338089011369311533887621625205800000000000000)
      linear := (-11948653622193509935401207094809003000000000000)
      constant := (104197328713243007017886575212993897088916534709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree036.table
  base := (-4745260475925185159256093108002225964453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (22079596)
      previous := (11039798)
      next := (11039798)
      square := (338089011369311533887621625205800000000000000)
      linear := (-11980016239203650151902841753919003000000000000)
      constant := (104747861322603004858951233459393943310581149987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36969619850464133481/12500000000000000000)
  centralHi := (295756958803713067849/100000000000000000000)
  directionLo := (74988075629557409307/25000000000000000000)
  directionHi := (299952302518229637229/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree037.table
  base := (-85523928200627291175458290067214804877/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-497368918685870327920732337339428171500000000000)
      constant := (4466280603433721823027382553025897172411466393075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree037.table
  base := (-2145114838883995460678705173335089879693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-498674387618917414432612880024881921500000000000)
      constant := (4489856469339260818407235598922411338847998505707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74988075629557409307/25000000000000000000)
  centralHi := (299952302518229637229/100000000000000000000)
  directionLo := (152044885552880296803/50000000000000000000)
  directionHi := (304089771105760593607/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree038.table
  base := (-189749660908323782031361269793315587529/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-510817365672903503457715787339091721500000000000)
      constant := (4719494722719748570154251807119893477128344786710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree038.table
  base := (-3807988351077008477862620522381390204201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1024316235100173995426321338032088443000000000000)
      constant := (9488767475057095482712371015391875786055311023599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152044885552880296803/50000000000000000000)
  centralHi := (304089771105760593607/100000000000000000000)
  directionLo := (308171695644360225553/100000000000000000000)
  directionHi := (154085847822180112777/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree039.table
  base := (-3287909364197945244478290641475310168201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3042801102323803804988594626852200000000000000)
      linear := (-116503513924430373109933163853056727000000000000)
      constant := (1106581706182241434834265268344882496981616695511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree039.table
  base := (-1649967413892112728452147176234233144721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1521400551161901902494297313426100000000000000)
      linear := (-58404649720139620110412050889689613500000000000)
      constant := (556205970579915371115223358560282421923062593231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308171695644360225553/100000000000000000000)
  centralHi := (154085847822180112777/50000000000000000000)
  directionLo := (312200254806889150359/100000000000000000000)
  directionHi := (7805006370172228759/2500000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree040.table
  base := (-2756208899319811801153857342325818010391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1075428519293939709063365374676837643000000000000)
      constant := (10493269191562698563298453367459580013090058899409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree040.table
  base := (-691832433182177700958732985253817950263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-539125577412426164274256246998368821500000000000)
      constant := (5274251629772783332912263232811311849954006162274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312200254806889150359/100000000000000000000)
  centralHi := (7805006370172228759/2500000000000000000)
  directionLo := (63235497691297672859/20000000000000000000)
  directionHi := (39522186057061045537/12500000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree041.table
  base := (-1100515859647697097341290486068904400331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-551162706634003030068666137338082371500000000000)
      constant := (5520532064475426310636321730469685470176626441469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree041.table
  base := (-442261909453310597115677955565016240223/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1105218614687191495109608071979062243000000000000)
      constant := (11099128098470661213586455007391290996834040395885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63235497691297672859/20000000000000000000)
  centralHi := (39522186057061045537/12500000000000000000)
  directionLo := (320105309721377714103/100000000000000000000)
  directionHi := (40013163715172214263/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree042.table
  base := (-202925720044688557844701873968919397769/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 266805000000000000000000000000000000000000000
      center := (2027718)
      previous := (1013859)
      next := (1013859)
      square := (31048990840038814336618312518900000000000000)
      linear := (-1280297400501215885727096569926861500000000000)
      constant := (13154870723585702128838932916075942218062593564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree042.table
  base := (-326579767174894148677627899494061183879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (4055436)
      previous := (2027718)
      next := (2027718)
      square := (62097981680077628673236625037800000000000000)
      linear := (-2567315361790318960704543423948723000000000000)
      constant := (26447977045252963079637556446572628005835163405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320105309721377714103/100000000000000000000)
  centralHi := (40013163715172214263/12500000000000000000)
  directionLo := (161992757875919776023/50000000000000000000)
  directionHi := (323985515751839552047/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree043.table
  base := (-256064499120035408851420993352605926597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-578059600608069381142633037337409471500000000000)
      constant := (6088921462790015450413178781286363129548056300006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree043.table
  base := (-1033021268006633085229902186248456123761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1159153534411869828231799227943711443000000000000)
      constant := (12241770859028000114042228672551646206055975272039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161992757875919776023/50000000000000000000)
  centralHi := (323985515751839552047/100000000000000000000)
  directionLo := (163909898665510585539/50000000000000000000)
  directionHi := (327819797331021171079/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree044.table
  base := (-50553044512409400106607151679221023097/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 972405000000000000000000000000000000000000000
      center := (7390278)
      previous := (3695139)
      next := (3695139)
      square := (113162024466587744813625420006900000000000000)
      linear := (-4888496261116550055203442044108041500000000000)
      constant := (52755311156393389912523490316527707164828289372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree044.table
  base := (-82501910834683213784084484203943933707/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1944810000000000000000000000000000000000000000
      center := (14780556)
      previous := (7390278)
      next := (7390278)
      square := (226324048933175489627250840013800000000000000)
      linear := (-9802652845241396651180948809306083000000000000)
      constant := (106064028505569309251029112327952965899143644665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163909898665510585539/50000000000000000000)
  centralHi := (327819797331021171079/100000000000000000000)
  directionLo := (165804873742690474133/50000000000000000000)
  directionHi := (331609747485380948267/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree045.table
  base := (58835333848352382994992192343766245443/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (11039798)
      previous := (5519899)
      next := (5519899)
      square := (169044505684655766943810812602900000000000000)
      linear := (-7468598698544885582920986880700451500000000000)
      constant := (82527193591564578415799077062217483501784691606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree045.table
  base := (28485699581588515827551318093451140509/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (11039798)
      previous := (5519899)
      next := (5519899)
      square := (169044505684655766943810812602900000000000000)
      linear := (-7488200334176223218234508542644201500000000000)
      constant := (82959691244196190835406131811852846325167260756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165804873742690474133/50000000000000000000)
  centralHi := (331609747485380948267/100000000000000000000)
  directionLo := (2682854953753371283/800000000000000000)
  directionHi := (41919608652396426297/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree046.table
  base := (447179645795109364066379309935521292323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-618404941569168907753583387336400121500000000000)
      constant := (6992843557334216007570957333033464266840724592923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree046.table
  base := (443743700914172244154646294643237888607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-620027956999443663957542980945342621500000000000)
      constant := (7029461265000245959577883507863826048785515534007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2682854953753371283/800000000000000000)
  centralHi := (41919608652396426297/12500000000000000000)
  directionLo := (67812516495894991313/20000000000000000000)
  directionHi := (169531291239737478283/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree047.table
  base := (196502061637981410581883662505019052739/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-631853388556202083290566837336063671500000000000)
      constant := (7307808066328336213887962841976598688556534994156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree047.table
  base := (1565685725097640788286265471819988325813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1267023373861226494476181539873009843000000000000)
      constant := (14692090736647003328782145241131213634600685004413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67812516495894991313/20000000000000000000)
  centralHi := (169531291239737478283/50000000000000000000)
  directionLo := (137091292177332447/40000000000000000)
  directionHi := (342728230443331117501/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree048.table
  base := (1133880064935242651241064205792813730333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1521400551161901902494297313426100000000000000)
      linear := (-71700203949248362091950031926191913500000000000)
      constant := (847732189275591458972471644535670404339750661437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree048.table
  base := (1130965256786956533554326661996772412941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1521400551161901902494297313426100000000000000)
      linear := (-71888379651309203390959839880851913500000000000)
      constant := (852164536530234837058769285178826426863620290349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137091292177332447/40000000000000000)
  centralHi := (342728230443331117501/100000000000000000000)
  directionLo := (346355085205895886277/100000000000000000000)
  directionHi := (173177542602947943139/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree049.table
  base := (2981091687548645371701911911562410143583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (744876)
      previous := (372438)
      next := (372438)
      square := (11405751737157115470594482149800000000000000)
      linear := (-548729931303847092348632850758343000000000000)
      constant := (6629056729046509177153269169945073931817256983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree049.table
  base := (1487862940514582107634877840916531068099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (372438)
      previous := (186219)
      next := (186219)
      square := (5702875868578557735297241074900000000000000)
      linear := (-275085025736340030736853955817921500000000000)
      constant := (3331845819116570756804361100755020170998438299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346355085205895886277/100000000000000000000)
  centralHi := (173177542602947943139/50000000000000000000)
  directionLo := (174972176468967288383/50000000000000000000)
  directionHi := (349944352937934576767/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree050.table
  base := (927890403685788360843970767786611973023/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-672198729517301609901517187335054321500000000000)
      constant := (8293581476081474043009522613596396487366367627246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree050.table
  base := (3706624773837725517812365428399344864269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1347925753448243994159468273819983643000000000000)
      constant := (16673766114051863435172445154676963516614295826069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174972176468967288383/50000000000000000000)
  centralHi := (349944352937934576767/100000000000000000000)
  directionLo := (8837429464298288003/2500000000000000000)
  directionHi := (353497178571931520121/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree051.table
  base := (4458764514002244576041537276339813282459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3042801102323803804988594626852200000000000000)
      linear := (-152366039223185507875222363852159527000000000000)
      constant := (1919062567137018344013264284396228003301699440251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree051.table
  base := (890844832438548385279278789865308401821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3042801102323803804988594626852200000000000000)
      linear := (-152765912590064795635618205755812027000000000000)
      constant := (1929075516147563905097350322015764106299244743345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8837429464298288003/2500000000000000000)
  centralHi := (353497178571931520121/100000000000000000000)
  directionLo := (357014650068428371059/100000000000000000000)
  directionHi := (17850732503421418553/5000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree052.table
  base := (5222334805141862614050615068463058462879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1398191246982735921950968174668762843000000000000)
      constant := (17969557059744946738195997147276103713823219666679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree052.table
  base := (5218160704867110146367724048651097028863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1401860673172922327281659429784632843000000000000)
      constant := (18063255667007620124908102324887376380153706917463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357014650068428371059/100000000000000000000)
  centralHi := (17850732503421418553/5000000000000000000)
  directionLo := (360497802307654412021/100000000000000000000)
  directionHi := (180248901153827206011/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree053.table
  base := (1200388562901070156190160645803856784511/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1425088140956802273024935074668089943000000000000)
      constant := (18681137060751540159997413088750322069891632693555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree053.table
  base := (749763355110705212290853373565321831029/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-714414066517630746921377503883478721500000000000)
      constant := (9389243235429895240479089682674544518079849859316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360497802307654412021/100000000000000000000)
  centralHi := (180248901153827206011/50000000000000000000)
  directionLo := (72789524129180842869/20000000000000000000)
  directionHi := (181973810322952107173/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree054.table
  base := (106207675755061227382702593686250039567/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (11039798)
      previous := (5519899)
      next := (5519899)
      square := (169044505684655766943810812602900000000000000)
      linear := (-8962870585993016198141370213996401500000000000)
      constant := (119791951304174210712222841649129337277841421024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree054.table
  base := (6793767266068060621167338816503144137229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (22079596)
      previous := (11039798)
      next := (11039798)
      square := (338089011369311533887621625205800000000000000)
      linear := (-17972785097501242721035192416657803000000000000)
      constant := (240831667996632837282397047908877696937891906309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72789524129180842869/20000000000000000000)
  centralHi := (181973810322952107173/50000000000000000000)
  directionLo := (367365044171300169113/100000000000000000000)
  directionHi := (183682522085650084557/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree055.table
  base := (3804056006226249694219590438421707398263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 972405000000000000000000000000000000000000000
      center := (7390278)
      previous := (3695139)
      next := (3695139)
      square := (113162024466587744813625420006900000000000000)
      linear := (-6111082350846838740383755680441091500000000000)
      constant := (83243916952370595187441345217315115201521586503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree055.table
  base := (7604875756542688163897218381787259653/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 972405000000000000000000000000000000000000000
      center := (7390278)
      previous := (3695139)
      next := (3695139)
      square := (113162024466587744813625420006900000000000000)
      linear := (-6127120052727024078367546131122341500000000000)
      constant := (83677212036265986773058980202216372772287546500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367365044171300169113/100000000000000000000)
  centralHi := (183682522085650084557/50000000000000000000)
  directionLo := (370750968689425874543/100000000000000000000)
  directionHi := (23171935543089117159/6250000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree056.table
  base := (4217081672230532655085176357811089765047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (18249462)
      previous := (9124731)
      next := (9124731)
      square := (279440917560349329029564812670100000000000000)
      linear := (-15365090029377564553539140557817053500000000000)
      constant := (213238028011651308092969800259093689048574056703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree056.table
  base := (8431192305063029683043118520521294803033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (36498924)
      previous := (18249462)
      next := (18249462)
      square := (558881835120698658059129625340200000000000000)
      linear := (-30810826788209775378082484524774107000000000000)
      constant := (428694723226701050001650575646904323307861795217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370750968689425874543/100000000000000000000)
  centralHi := (23171935543089117159/6250000000000000000)
  directionLo := (187053124732864303733/50000000000000000000)
  directionHi := (374106249465728607467/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree057.table
  base := (2318806806850719634670381444847270242551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1521400551161901902494297313426100000000000000)
      linear := (-85148650936281537628933481925855463500000000000)
      constant := (1203510417159002364940053710958877219741450863278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree057.table
  base := (4636250269662104017440080541564771420471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1521400551161901902494297313426100000000000000)
      linear := (-85372109582478786671507628872014213500000000000)
      constant := (1209768244000368809480529786254923263870619898519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187053124732864303733/50000000000000000000)
  centralHi := (374106249465728607467/100000000000000000000)
  directionLo := (188715851874239943789/50000000000000000000)
  directionHi := (377431703748479887579/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree058.table
  base := (10131107057594339461008993750037157121427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1559572610827134028394769574664725443000000000000)
      constant := (22442605567116927356294800515413420195350001570827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree058.table
  base := (405144215780381178224609643498450717717/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1563665432346957326648232897678580443000000000000)
      constant := (22559241584166755694981221177753210405947767627925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188715851874239943789/50000000000000000000)
  centralHi := (377431703748479887579/100000000000000000000)
  directionLo := (380728113093381387143/100000000000000000000)
  directionHi := (47591014136672673393/12500000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree059.table
  base := (11001625541458298105446944877321668474421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1586469504801200379468736474664052543000000000000)
      constant := (23235576747798389053091216104877151237445438330621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree059.table
  base := (10999331015032079244674679654992366625083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1590632892209296493209328475660905043000000000000)
      constant := (23356276876319684573372178655513203024387144797683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380728113093381387143/100000000000000000000)
  centralHi := (47591014136672673393/12500000000000000000)
  directionLo := (76799245101709933009/20000000000000000000)
  directionHi := (191998112754274832523/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree060.table
  base := (5943311399466508153627556451543323735933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1521400551161901902494297313426100000000000000)
      linear := (-89631466598625929474594631925743313500000000000)
      constant := (1335672071587593274689343028181696609095782919837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree060.table
  base := (2376903772580311110530959272989730879371/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3042801102323803804988594626852200000000000000)
      linear := (-179733372452403962196713783738136627000000000000)
      constant := (2685214504190841254072396605340797102216258403095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76799245101709933009/20000000000000000000)
  centralHi := (191998112754274832523/50000000000000000000)
  directionLo := (96809189359139368223/25000000000000000000)
  directionHi := (387236757436557472893/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree061.table
  base := (2557190930631724009543458720092911198531/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1640263292749333081616670274662706743000000000000)
      constant := (24862163796652950926002568242769886866744911983655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree061.table
  base := (12784026012369086105972642362905118850837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1644567811933974826331519631625554243000000000000)
      constant := (24991199205002965296954112612800073961226785302237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96809189359139368223/25000000000000000000)
  centralHi := (387236757436557472893/100000000000000000000)
  directionLo := (390450395588409629807/100000000000000000000)
  directionHi := (24403149724275601863/6250000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree062.table
  base := (3424872772036376854188202402527743303331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-833580093361699716345318587331016921500000000000)
      constant := (12847886606232402235908197442769476403730778123062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree062.table
  base := (13697723612506445238905973448747534509813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1671535271796313992892615209607878843000000000000)
      constant := (25829079846029924561340673489023730971339355988413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390450395588409629807/100000000000000000000)
  centralHi := (24403149724275601863/6250000000000000000)
  directionLo := (39363779864275215577/10000000000000000000)
  directionHi := (393637798642752155771/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree063.table
  base := (1462711485792609473629695345679030929831/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (225302)
      previous := (112651)
      next := (112651)
      square := (3449887871115423815179812502100000000000000)
      linear := (-213411070886554016599219460148823500000000000)
      constant := (3343779639324334084561995017418025996914839995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree063.table
  base := (7312747750591225636991947318996505546903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (225302)
      previous := (112651)
      next := (112651)
      square := (3449887871115423815179812502100000000000000)
      linear := (-213971117618877949036748650490073500000000000)
      constant := (3361119895092949045629817309689267031387587887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39363779864275215577/10000000000000000000)
  centralHi := (393637798642752155771/100000000000000000000)
  directionLo := (198399799411112190109/50000000000000000000)
  directionHi := (396799598822224380219/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree064.table
  base := (3113744046462342856370499596206606635047/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1720953974671532134838570974660688043000000000000)
      constant := (27403610002064177903497651557486603476319298242235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree064.table
  base := (7783618477763903875649111537608392379067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-862735095760496163007403182786264021500000000000)
      constant := (13772833192148535302268706879085238324751072836467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198399799411112190109/50000000000000000000)
  centralHi := (396799598822224380219/100000000000000000000)
  directionLo := (24996025209852469769/6250000000000000000)
  directionHi := (79987280671527903261/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree065.table
  base := (16524211865837755922456627190926776788859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1747850868645598485912537874660015143000000000000)
      constant := (28277832644099008648561546903758195926427564548659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree065.table
  base := (413071339136194325266692489096049925419/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-876218825691665746287950971777426321500000000000)
      constant := (14212183797750160956266993131374005344269898344380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24996025209852469769/6250000000000000000)
  centralHi := (79987280671527903261/20000000000000000000)
  directionLo := (201524397924798954969/50000000000000000000)
  directionHi := (403048795849597909939/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree066.table
  base := (4373375944449475815891724216968265001879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 108045000000000000000000000000000000000000000
      center := (821142)
      previous := (410571)
      next := (410571)
      square := (12573558274065304979291713334100000000000000)
      linear := (-814852048953014158396007701863793500000000000)
      constant := (13390995720728095977538491453946611726851206622) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree066.table
  base := (2186532527258199093130875191361911737979/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 108045000000000000000000000000000000000000000
      center := (821142)
      previous := (410571)
      next := (410571)
      square := (12573558274065304979291713334100000000000000)
      linear := (-816990409203705536793846428621293500000000000)
      constant := (13460363341581386582928466974815866702983952844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201524397924798954969/50000000000000000000)
  centralHi := (403048795849597909939/100000000000000000000)
  directionLo := (10153433438404505239/2500000000000000000)
  directionHi := (406137337536180209561/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree067.table
  base := (923825921622832426766093238006663435649/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-900822328296865594030235837329334671500000000000)
      constant := (15033438142209009211686036402540685526695428334490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree067.table
  base := (3695076036434569153353690208959641542761/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1806372571108009825698093099519501843000000000000)
      constant := (30222575866034665259509203665084148871861009734805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10153433438404505239/2500000000000000000)
  centralHi := (406137337536180209561/100000000000000000000)
  directionLo := (25575160529657443921/6250000000000000000)
  directionHi := (409202568474519102737/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree068.table
  base := (9736592954800445510946825473838540264731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-914270775283898769567219287328998221500000000000)
      constant := (15490846906369588076281578303616565295556243102931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree068.table
  base := (778885771313542752008755520845972733653/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-1833340030970348992259188677501826443000000000000)
      constant := (31142079491873158169281646763202273084221046506325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25575160529657443921/6250000000000000000)
  centralHi := (409202568474519102737/100000000000000000000)
  directionLo := (103061252160823582199/25000000000000000000)
  directionHi := (412245008643294328797/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree069.table
  base := (20483443156557794287252847354379441711733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3042801102323803804988594626852200000000000000)
      linear := (-206159827171318210023156163850813727000000000000)
      constant := (3545559975660121716933257568932511209819809446037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree069.table
  base := (20482490157298812208578103903168102925787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3042801102323803804988594626852200000000000000)
      linear := (-206700832314743128757809361720461227000000000000)
      constant := (3563908974216293614280888912987027904370923085243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103061252160823582199/25000000000000000000)
  centralHi := (412245008643294328797/100000000000000000000)
  directionLo := (83053031794504922017/20000000000000000000)
  directionHi := (207632579486262305043/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree070.table
  base := (2150723331367753497969337490467511003261/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (18249462)
      previous := (9124731)
      next := (9124731)
      square := (279440917560349329029564812670100000000000000)
      linear := (-19207503454244186135534411986292353500000000000)
      constant := (335223600520317019287282818355425372209025459945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree070.table
  base := (21506361584122566358685823052950737655427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (36498924)
      previous := (18249462)
      next := (18249462)
      square := (558881835120698658059129625340200000000000000)
      linear := (-38515815320306680109824078234009707000000000000)
      constant := (673915885127369455325057146012255653808281161323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83053031794504922017/20000000000000000000)
  centralHi := (207632579486262305043/50000000000000000000)
  directionLo := (209131751153215886743/50000000000000000000)
  directionHi := (418263502306431773487/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree071.table
  base := (5636126276516360621946587797746697639219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-954616116244998296178169637327988871500000000000)
      constant := (16903655908138982911584706742264957263989653982038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree071.table
  base := (18034966302750553457350531749572923069/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-957121205278683245971237705724400121500000000000)
      constant := (16991085554514976719120865927063005088885778043125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209131751153215886743/50000000000000000000)
  centralHi := (418263502306431773487/100000000000000000000)
  directionLo := (421240504304617860569/100000000000000000000)
  directionHi := (42124050430461786057/10000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree072.table
  base := (5898803073764177630696251438002921970273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (11039798)
      previous := (5519899)
      next := (5519899)
      square := (169044505684655766943810812602900000000000000)
      linear := (-11951414360889277428582136880588301500000000000)
      constant := (214668120917927376902676277388216326787451364466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree072.table
  base := (23594483346715063759670310407349562138567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (22079596)
      previous := (11039798)
      next := (11039798)
      square := (338089011369311533887621625205800000000000000)
      linear := (-23965553955798835290167543079396603000000000000)
      constant := (431556270444985751199115943062254918142058623407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421240504304617860569/100000000000000000000)
  centralHi := (42124050430461786057/10000000000000000000)
  directionLo := (26512288392894864009/6250000000000000000)
  directionHi := (84839322857263564829/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree073.table
  base := (2465931318356593953997490234398310339743/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-981513010219064647252136537327315971500000000000)
      constant := (17879341593522840429547308977312537381251052821715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree073.table
  base := (12329323397617872389243946818805647453069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-984088665141022412532333283706724721500000000000)
      constant := (17971768896451970931811928649527402439050757774869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26512288392894864009/6250000000000000000)
  centralHi := (84839322857263564829/20000000000000000000)
  directionLo := (427132266022061859361/100000000000000000000)
  directionHi := (213566133011030929681/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree074.table
  base := (3217096271252509871255160152955497906177/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-994961457206097822789119987326979521500000000000)
      constant := (18377326863227264141786158589593485305382945222308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree074.table
  base := (12868080543485760859177072016381877766283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-997572395072191995812881072697887021500000000000)
      constant := (18472304947847108633440341095131696118853602578883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427132266022061859361/100000000000000000000)
  centralHi := (213566133011030929681/50000000000000000000)
  directionLo := (215023939238348377897/50000000000000000000)
  directionHi := (86009575695339351159/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree075.table
  base := (26827549346103045284006625869985242471303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3042801102323803804988594626852200000000000000)
      linear := (-224091089820695777405800763850365127000000000000)
      constant := (4196016267665940853614440707480391774902048769767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree075.table
  base := (2682699274209479226875054427920395853739/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1521400551161901902494297313426100000000000000)
      linear := (-112339569444817953232603206854338813500000000000)
      constant := (2108848523697813304109982216556818053322084860855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215023939238348377897/50000000000000000000)
  centralHi := (86009575695339351159/20000000000000000000)
  directionLo := (216471928253684928923/50000000000000000000)
  directionHi := (432943856507369857847/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree076.table
  base := (872863129187779851975029452317932781891/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-1021858351180164173863086887326306621500000000000)
      constant := (19393580257549712436541648136028263183547170753456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree076.table
  base := (27931111577831167188515744536182188815609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-2049079709869062324747953301360423243000000000000)
      constant := (38987527675236094819645604064448962757828862925409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216471928253684928923/50000000000000000000)
  centralHi := (432943856507369857847/100000000000000000000)
  directionLo := (27238786969985493351/6250000000000000000)
  directionHi := (435820591519767893617/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree077.table
  base := (29048954959323546784792599008292959562757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (301644)
      previous := (150822)
      next := (150822)
      square := (4618858141493377339331649796200000000000000)
      linear := (-349234878788057800438546242983967000000000000)
      constant := (6716764276587239160345951465567042506504582533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree077.table
  base := (29048490383777312069912072974438105429261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (301644)
      previous := (150822)
      next := (150822)
      square := (4618858141493377339331649796200000000000000)
      linear := (-350151318895496962609048554451467000000000000)
      constant := (6751454208365643910866141986976541340448736909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27238786969985493351/6250000000000000000)
  centralHi := (435820591519767893617/100000000000000000000)
  directionLo := (109669615521405558327/25000000000000000000)
  directionHi := (438678462085622233309/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree078.table
  base := (15089764478017241439379284079787346969563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1521400551161901902494297313426100000000000000)
      linear := (-116528360572692280548561531925070413500000000000)
      constant := (2270763914788911979238622411991243795210499710907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree078.table
  base := (30179104629192040624302678116926710028267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3042801102323803804988594626852200000000000000)
      linear := (-233668292177082295318904939702785827000000000000)
      constant := (4564978425309970109210698758006956413517099413963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109669615521405558327/25000000000000000000)
  centralHi := (438678462085622233309/100000000000000000000)
  directionLo := (441517834524238696771/100000000000000000000)
  directionHi := (110379458631059674193/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree079.table
  base := (1957707481282182853555246112046656893791/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-1062203692141263700474037237325297271500000000000)
      constant := (20968662599183077454357789478989066800346803711928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree079.table
  base := (122355203902781612475157054435074873669/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-1064991044728039912215620017653698521500000000000)
      constant := (21076914316995909491228580502886831597035249980032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441517834524238696771/100000000000000000000)
  centralHi := (110379458631059674193/25000000000000000000)
  directionLo := (222169531725290442047/50000000000000000000)
  directionHi := (88867812690116176819/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree080.table
  base := (6496061394326940287723708857805551868723/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-2151304278256593752022041374649921643000000000000)
      constant := (43014419116535259134736656624894197267453576246615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree080.table
  base := (1623997657822704246936601435615105608031/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-1078474774659209495496167806644860821500000000000)
      constant := (21618219975421356604325189999375427458044127062310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222169531725290442047/50000000000000000000)
  centralHi := (88867812690116176819/20000000000000000000)
  directionLo := (447142492292228547167/100000000000000000000)
  directionHi := (13973202884132142099/3125000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree081.table
  base := (6730094506886574479167901253883166812781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (22079596)
      previous := (11039798)
      next := (11039798)
      square := (338089011369311533887621625205800000000000000)
      linear := (-26891372496674816087605040427768503000000000000)
      constant := (544506565328382250472080806410873244278079744505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree081.table
  base := (33650149527543640970222405382179278548751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (22079596)
      previous := (11039798)
      next := (11039798)
      square := (338089011369311533887621625205800000000000000)
      linear := (-26961938384947631574733718410766003000000000000)
      constant := (547316535251633278207304105453537036683261689271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447142492292228547167/100000000000000000000)
  centralHi := (13973202884132142099/3125000000000000000)
  directionLo := (224964226888672227921/50000000000000000000)
  directionHi := (449928453777344455843/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree082.table
  base := (34833799945037573079395883265216308392813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-2205098066204726454169975174648575843000000000000)
      constant := (45209162836596766413226869830689388716077662471413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree082.table
  base := (34833505108764709206805949525456891482051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-2210884469043097324114526769254370843000000000000)
      constant := (45442426466303816105890052339122988588190812024251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224964226888672227921/50000000000000000000)
  centralHi := (449928453777344455843/100000000000000000000)
  directionLo := (452697270395612510761/100000000000000000000)
  directionHi := (226348635197806255381/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree083.table
  base := (225189214842164115021332599790186522139/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-1115997480089396402621971037323951471500000000000)
      constant := (23163405951288331324764635060935469652942271835120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree083.table
  base := (36030005292249250529626875221870793615541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-2237851928905436490675622347236695443000000000000)
      constant := (46565800939851988043924862146621694642890427535741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452697270395612510761/100000000000000000000)
  centralHi := (226348635197806255381/50000000000000000000)
  directionLo := (22772462741697736071/5000000000000000000)
  directionHi := (455449254833954721421/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree084.table
  base := (930997061284611859384137183279546220841/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 266805000000000000000000000000000000000000000
      center := (2027718)
      previous := (1013859)
      next := (1013859)
      square := (31048990840038814336618312518900000000000000)
      linear := (-2561101875456756413058853712751961500000000000)
      constant := (53807232057666614443002688732501775817805932020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree084.table
  base := (4654954613591536587036195581674546052767/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 266805000000000000000000000000000000000000000
      center := (2027718)
      previous := (1013859)
      next := (1013859)
      square := (31048990840038814336618312518900000000000000)
      linear := (-2567822436244643602309203996846961500000000000)
      constant := (54084764700822019274182072068276282807686799548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22772462741697736071/5000000000000000000)
  centralHi := (455449254833954721421/100000000000000000000)
  directionLo := (229092355194346756381/50000000000000000000)
  directionHi := (458184710388693512763/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree085.table
  base := (38462612116246096603000356598904217323737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-2285788748126925507391875874646557143000000000000)
      constant := (48602662869684743961694688925778088045559861155137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree085.table
  base := (1201949627683812077892695537207181788767/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-1145893424315057411898906751600672321500000000000)
      constant := (24426655382870407779595164434502966134198873378672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229092355194346756381/50000000000000000000)
  centralHi := (458184710388693512763/100000000000000000000)
  directionLo := (230451965677848618031/50000000000000000000)
  directionHi := (460903931355697236063/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree086.table
  base := (19849226247542330787056044509021637725651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-1156342821050495929232921387322942121500000000000)
      constant := (24880432115575039607759915604739629260059202187851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree086.table
  base := (19849124060290378903379486079234759297529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-1159377154246226995179454540591834621500000000000)
      constant := (25008722793415728820690606364219920043476071231329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230451965677848618031/50000000000000000000)
  centralHi := (460903931355697236063/100000000000000000000)
  directionLo := (463607203399929486731/100000000000000000000)
  directionHi := (115901800849982371683/25000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree087.table
  base := (40947393781775724891108864028800628917347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3042801102323803804988594626852200000000000000)
      linear := (-259953615119450912171089963849467927000000000000)
      constant := (5659175836499807582625149297311218817873269110083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree087.table
  base := (20473603681891858103572548138418100392583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1521400551161901902494297313426100000000000000)
      linear := (-130317876019710730940000258842555213500000000000)
      constant := (2844175927907426857041053657253850565247382451687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463607203399929486731/100000000000000000000)
  centralHi := (115901800849982371683/25000000000000000000)
  directionLo := (233147401952857878861/50000000000000000000)
  directionHi := (466294803905715757723/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree088.table
  base := (21104713566702863464765024262431622710247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 972405000000000000000000000000000000000000000
      center := (7390278)
      previous := (3695139)
      next := (3695139)
      square := (113162024466587744813625420006900000000000000)
      linear := (-9778840620037704795924696589440241500000000000)
      constant := (215362882453041701385561711528504991416311546807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree088.table
  base := (42209257116715769366670467700079375410781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1944810000000000000000000000000000000000000000
      center := (14780556)
      previous := (7390278)
      next := (7390278)
      square := (226324048933175489627250840013800000000000000)
      linear := (-19609001886092002673397522621060483000000000000)
      constant := (432946065351621231312642908272363341009264099661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233147401952857878861/50000000000000000000)
  centralHi := (466294803905715757723/100000000000000000000)
  directionLo := (58620875288617886087/12500000000000000000)
  directionHi := (468967002308943088697/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree089.table
  base := (2717784035979067483669936653706457481281/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-1196688162011595455843871737321932771500000000000)
      constant := (26658284559455246815338286119843401829954665835848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree089.table
  base := (43484389537290858936425605716625329734181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-2399656688079471490042195815130643043000000000000)
      constant := (53591367017927368943289424908689426715496023862381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58620875288617886087/12500000000000000000)
  centralHi := (468967002308943088697/100000000000000000000)
  directionLo := (235812030206159410599/50000000000000000000)
  directionHi := (471624060412318821199/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree090.table
  base := (44772738917533416964850314140195530778777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (22079596)
      previous := (11039798)
      next := (11039798)
      square := (338089011369311533887621625205800000000000000)
      linear := (-29879916271571077318045807094360403000000000000)
      constant := (673195519198777003377856817874941578297381072817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree090.table
  base := (44772597555746689144266886190625695861263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (22079596)
      previous := (11039798)
      next := (11039798)
      square := (338089011369311533887621625205800000000000000)
      linear := (-29958322814096427859299893742135403000000000000)
      constant := (676664763791484147207238652959709412787309988023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235812030206159410599/50000000000000000000)
  centralHi := (471624060412318821199/100000000000000000000)
  directionLo := (237133116342366273221/50000000000000000000)
  directionHi := (474266232684732546443/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree091.table
  base := (46074003674344350279893017252079691508013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (36498924)
      previous := (18249462)
      next := (18249462)
      square := (558881835120698658059129625340200000000000000)
      linear := (-49942247183088237017054638258010607000000000000)
      constant := (1137849412440998975428900907170271713017031735237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree091.table
  base := (23036937399293723610425842541179393253649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (18249462)
      previous := (9124731)
      next := (9124731)
      square := (279440917560349329029564812670100000000000000)
      linear := (-25036649059226018603718234398931553500000000000)
      constant := (571856227603186993791571148748233762180671678601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237133116342366273221/50000000000000000000)
  centralHi := (474266232684732546443/100000000000000000000)
  directionLo := (476893766545690125933/100000000000000000000)
  directionHi := (238446883272845062967/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree092.table
  base := (47388332998406714563762527589553954852083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-2474067005945389964909644174641846843000000000000)
      constant := (56993921444825487314375779654098216396924142424683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree092.table
  base := (4738821552001638099756926385861743591381/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-1240279533833244494862741274538808421500000000000)
      constant := (28643780098361226634736708090769444645014197797905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476893766545690125933/100000000000000000000)
  centralHi := (238446883272845062967/50000000000000000000)
  directionLo := (479506902635719640971/100000000000000000000)
  directionHi := (119876725658929910243/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree093.table
  base := (48715721616440118794552036999940149423269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3042801102323803804988594626852200000000000000)
      linear := (-277884877768828479553734563849019327000000000000)
      constant := (6471859737406517304199911271490857089105377798341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree093.table
  base := (48715614540120664945230472192095271921809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3042801102323803804988594626852200000000000000)
      linear := (-278614058614314239587397569673326827000000000000)
      constant := (6505199491116205531628205694427890542945962852401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479506902635719640971/100000000000000000000)
  centralHi := (119876725658929910243/25000000000000000000)
  directionLo := (482105875073585715363/100000000000000000000)
  directionHi := (120526468768396428841/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree094.table
  base := (12514041193288878739743278906048474631513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-1263930396946761333528788987320250521500000000000)
      constant := (29756534836603018687669527908442186106294329700226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree094.table
  base := (5005606718914361813508441372227496504551/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-1267246993695583661423836852521133021500000000000)
      constant := (29909807932596431050203522505088711610859457733755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (482105875073585715363/100000000000000000000)
  centralHi := (120526468768396428841/25000000000000000000)
  directionLo := (484690911701090344689/100000000000000000000)
  directionHi := (48469091170109034469/10000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree095.table
  base := (25704829090188616539679242359539391467679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13692604960457117122448675820834900000000000000)
      linear := (-1277378843933794509065772437319914071500000000000)
      constant := (30396458726778710218885605429994662410560107231479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree095.table
  base := (51409569257244817372685132048607791941941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-2561461447253506489408769283024590643000000000000)
      constant := (61106021433096679200196233132863165227643935942141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484690911701090344689/100000000000000000000)
  centralHi := (48469091170109034469/10000000000000000000)
  directionLo := (60907779289523086907/12500000000000000000)
  directionHi := (487262234316184695257/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree096.table
  base := (6597024746395276231902003326521877819441/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1521400551161901902494297313426100000000000000)
      linear := (-143425254546758631622528431924397513500000000000)
      constant := (3449237827039729083552931258930529844775345475396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree096.table
  base := (52776116949207680413598437285535360513693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3042801102323803804988594626852200000000000000)
      linear := (-287603211901760628441096095667435027000000000000)
      constant := (6934001337160833514679151014472123758246187436477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60907779289523086907/12500000000000000000)
  centralHi := (487262234316184695257/100000000000000000000)
  directionLo := (489820058895066892151/100000000000000000000)
  directionHi := (61227507361883361519/12500000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree097.table
  base := (54155780658425595561919015892253251389277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-2608551475815721720279478674638482343000000000000)
      constant := (63393159890620364986109000466816152269345995608677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree097.table
  base := (54155706843607312692557658299929662526519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27385209920914234244897351641669800000000000000)
      linear := (-2615396366978184822530960438989239843000000000000)
      constant := (63719587588731671070841760078629602962936212938319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell069.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489820058895066892151/100000000000000000000)
  centralHi := (61227507361883361519/12500000000000000000)
  directionLo := (123091148950973806319/25000000000000000000)
  directionHi := (492364595803895225277/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree098.table
  base := (27774201548815065290308185451670305791809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (372438)
      previous := (186219)
      next := (186219)
      square := (5702875868578557735297241074900000000000000)
      linear := (-548823067428110802031121527413121500000000000)
      constant := (13476375341789933785693447987420533917065520009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree098.table
  base := (3471770990999961801904246164954663237021/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (372438)
      previous := (186219)
      next := (186219)
      square := (5702875868578557735297241074900000000000000)
      linear := (-550263187596943771156196588290621500000000000)
      constant := (13545761770796631336579378304435209735088342568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell069.Kernel098
