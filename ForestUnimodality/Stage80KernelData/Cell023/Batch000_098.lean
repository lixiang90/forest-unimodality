import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell023.Parameters
import ForestUnimodality.BinomialMassData.Q65_153.Batch000_049
import ForestUnimodality.BinomialMassData.Q65_153.Batch050_099
import ForestUnimodality.BinomialMassData.Q22_51.Batch000_049
import ForestUnimodality.BinomialMassData.Q22_51.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree000.table
  base := (23814539808773818931042499/1250000000000000000000000)
  polynomial :=
    { denominator := 34000000000000000000000000000000000000000
      center := (88)
      previous := (65)
      next := (0)
      square := (2823698946407966481331186502000000000000)
      linear := (9421158254943874821307758960000000000000)
      constant := (647755482798647874924355972800000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree000.table
  base := (23814539808773818931042499/1250000000000000000000000)
  polynomial :=
    { denominator := 34000000000000000000000000000000000000000
      center := (87)
      previous := (66)
      next := (0)
      square := (2823698946407966481331186502000000000000)
      linear := (9421158254943874821307758960000000000000)
      constant := (647755482798647874924355972800000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree001.table
  base := (12235034415651947708436154803588848306207/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (121176)
      previous := (89505)
      next := (0)
      square := (3888233449203769844793043813254000000000000)
      linear := (9669207149760394845783295880580000000000000)
      constant := (568010235931002112712723813248172699999999326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree001.table
  base := (60659775221485330279742011899480189243453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (5343544760402806360621852513080000000000000)
      constant := (312845130328053284652705295522815944444442506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49431818042324279781/100000000000000000000)
  directionHi := (24715909021162139891/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree002.table
  base := (79640529646631317947469223802644586483831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (31827396912315370313129038366200000000000000)
      constant := (1823226827469598687520155802987107124999999879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree002.table
  base := (78367340737834699576869061592559256055363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (3479903455773548482943269421760000000000000)
      constant := (199223336210917397131448948602726624999999163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49431818042324279781/100000000000000000000)
  centralHi := (24715909021162139891/50000000000000000000)
  directionLo := (69907147488214053033/100000000000000000000)
  directionHi := (34953573744107026517/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree003.table
  base := (52527349551164886579081233152410884228169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (67320)
      previous := (49725)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (1700973119536529599704621925500000000000000)
      constant := (130946868074766550389540005670170709877467569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree003.table
  base := (2566843469930288739457187672487080629933/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1479)
      previous := (1122)
      next := (0)
      square := (48002882088935430182630170534000000000000)
      linear := (35916936692095346783659696232000000000000)
      constant := (2840397939634263582447520267979065208202548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69907147488214053033/100000000000000000000)
  centralHi := (34953573744107026517/50000000000000000000)
  directionLo := (85618420359805567813/100000000000000000000)
  directionHi := (42809210179902783907/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree004.table
  base := (35021228966190568609157075046774500094171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-1209880760657837518445843707200000000000000)
      constant := (765726176338823018732453721565944272704448939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree004.table
  base := (8505238967405194189739823667791625650733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-247379153484967272413896760880000000000000)
      constant := (82483966920646929242229444868824073270226132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85618420359805567813/100000000000000000000)
  centralHi := (42809210179902783907/50000000000000000000)
  directionLo := (49431818042324279781/50000000000000000000)
  directionHi := (98863636084648559563/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree005.table
  base := (2934427546885374582205061204704950297783/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-17728519597144441434233284743900000000000000)
      constant := (499473205850687658200199827806255452166417976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree005.table
  base := (226776601942842881183273682067158241941/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (13311)
      previous := (10098)
      next := (0)
      square := (432025938800418871643671534806000000000000)
      linear := (-422204091622845030018495970440000000000000)
      constant := (10697745859025584130716886876933571745770820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49431818042324279781/50000000000000000000)
  centralHi := (98863636084648559563/100000000000000000000)
  directionLo := (110532905394037666001/100000000000000000000)
  directionHi := (55266452697018833001/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree006.table
  base := (15670801036409448153326504318738128370521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (67320)
      previous := (49725)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-3805239825959005038891191753400000000000000)
      constant := (36423939661588252137751240668037871891725121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree006.table
  base := (15051511178328141387659508775227367836561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-441629084749275891974562549280000000000000)
      constant := (3885079314521481314421531378920709304766129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110532905394037666001/100000000000000000000)
  centralHi := (55266452697018833001/50000000000000000000)
  directionLo := (60541365630898881203/50000000000000000000)
  directionHi := (121082731261797762407/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree007.table
  base := (10243729237366427073847001021279235079881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-50765797270117649265808166817300000000000000)
      constant := (218831440794625813463522460311875613984934329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree007.table
  base := (4884647134689728742973055477923682933769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-5838303067372740905449646034840000000000000)
      constant := (23343189476621304281151505246038998621466338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60541365630898881203/50000000000000000000)
  centralHi := (121082731261797762407/100000000000000000000)
  directionLo := (26156859478757149407/20000000000000000000)
  directionHi := (32696074348446436759/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree008.table
  base := (1587606090800400480868017169704866973283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-67284436106604253181595607854000000000000000)
      constant := (152769096960944962887942222550484923910326988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree008.table
  base := (5988735830840178044662323213316099398713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-7701944372001998783128229126160000000000000)
      constant := (16430402504120288191124464048715174536052513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26156859478757149407/20000000000000000000)
  centralHi := (32696074348446436759/25000000000000000000)
  directionLo := (139814294976428106067/100000000000000000000)
  directionHi := (34953573744107026517/25000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree009.table
  base := (866084480856085175257990811120041870611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7480)
      previous := (5525)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-1034605863494948853054111714700000000000000)
      constant := (1448178417769833493797998942404768402426316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree009.table
  base := (1594262445380586144971745176806127820797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-1062842852959028517867423579720000000000000)
      constant := (1430158119461177157432298962073941880420666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139814294976428106067/100000000000000000000)
  centralHi := (34953573744107026517/25000000000000000000)
  directionLo := (9268465882935802459/6250000000000000000)
  directionHi := (29659090825394567869/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree010.table
  base := (313396208954778584341784619861955233873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-100321713779577461013170489927400000000000000)
      constant := (104662407540277143812653717760394040278932228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree010.table
  base := (1042540825963050062531463916787680403551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-11429226981260514538485395308800000000000000)
      constant := (11818011448822629154219740931564756729636151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9268465882935802459/6250000000000000000)
  centralHi := (29659090825394567869/20000000000000000000)
  directionLo := (156317133896750300929/100000000000000000000)
  directionHi := (15631713389675030093/10000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree011.table
  base := (-246722736530227677113366228565190484339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-116840352616064064928957930964100000000000000)
      constant := (109895372149900588360428045809784911904216698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree011.table
  base := (-655754591685322809624966414920601016609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-13292868285889772416163978400120000000000000)
      constant := (12732961693767312421606416830911516755799991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156317133896750300929/100000000000000000000)
  centralHi := (15631713389675030093/10000000000000000000)
  directionLo := (32789358630302007243/20000000000000000000)
  directionHi := (20493349143938754527/12500000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree012.table
  base := (-1913434658842754605045504982366548360017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (67320)
      previous := (49725)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-14817665716950074316082819111200000000000000)
      constant := (14422418310180217039172913224864607715595783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree012.table
  base := (-509746025443182591554000451162708983199/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-1684056621168781143760284610160000000000000)
      constant := (1696813562701579659090722792375908415421956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32789358630302007243/20000000000000000000)
  centralHi := (20493349143938754527/12500000000000000000)
  directionLo := (85618420359805567813/50000000000000000000)
  directionHi := (171236840719611135627/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree013.table
  base := (-3095928105535488076385739736086661199383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-149877630289037272760532813037500000000000000)
      constant := (162285417571204880372747049384697347983643353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree013.table
  base := (-319360082760073655551172104695680436287/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (13311)
      previous := (10098)
      next := (0)
      square := (432025938800418871643671534806000000000000)
      linear := (-3404030179029657634304228916552000000000000)
      constant := (3841645597351194971079906177669070370435026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85618420359805567813/50000000000000000000)
  centralHi := (171236840719611135627/100000000000000000000)
  directionLo := (4455723864775153631/2500000000000000000)
  directionHi := (178228954591006145241/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree014.table
  base := (-4100483153297007578237010014657895691357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-166396269125523876676320254074200000000000000)
      constant := (205952152712882511900954615597873319761023987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree014.table
  base := (-4176868087624684789913133599937323221423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-18883792199777546049199727674080000000000000)
      constant := (24394737569790237976700468501283022301078777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4455723864775153631/2500000000000000000)
  centralHi := (178228954591006145241/100000000000000000000)
  directionLo := (92478463559864015899/50000000000000000000)
  directionHi := (184956927119728031799/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree015.table
  base := (-4967334810226199701906597728043297181621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (67320)
      previous := (49725)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-20323878662445608954678632790100000000000000)
      constant := (28873345434674223524585195048109384030603779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree015.table
  base := (-5027341398556894870289950395126685355979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-2305270389378533769653145640600000000000000)
      constant := (3414507546049806943739688870808387932122069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92478463559864015899/50000000000000000000)
  centralHi := (184956927119728031799/100000000000000000000)
  directionLo := (191448608050677252451/100000000000000000000)
  directionHi := (47862152012669313113/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree016.table
  base := (-1144818537470886888751753136428252935969/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (121176)
      previous := (89505)
      next := (0)
      square := (3888233449203769844793043813254000000000000)
      linear := (-39886709359699416901579027229520000000000000)
      constant := (64672594556825607917758488173351027021901679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree016.table
  base := (-1442851522311833766971181546415611297497/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-22611074809036061804556893856720000000000000)
      constant := (38147090780391280932767839983411980060841212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191448608050677252451/100000000000000000000)
  centralHi := (47862152012669313113/25000000000000000000)
  directionLo := (1581818177354376953/800000000000000000)
  directionHi := (98863636084648559563/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree017.table
  base := (-6389992419065551773179107097559175470417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (35640)
      previous := (26325)
      next := (0)
      square := (1143598073295226424939130533310000000000000)
      linear := (-12703069743234334613157798657900000000000000)
      constant := (23294732786104193274128489423411015377235791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree017.table
  base := (-6427403589128125200648621035614610305217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3915)
      previous := (2970)
      next := (0)
      square := (127066452588358491659903392590000000000000)
      linear := (-1439689183156783510719733938120000000000000)
      constant := (2740976477039197038090671859590964623301799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1581818177354376953/800000000000000000)
  centralHi := (98863636084648559563/50000000000000000000)
  directionLo := (203812607054815809951/100000000000000000000)
  directionHi := (6369143970462994061/3125000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree018.table
  base := (-87232855390035009328379151987772939693/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1496)
      previous := (1105)
      next := (0)
      square := (48002882088935430182630170534000000000000)
      linear := (-574002035732025413183876588200000000000000)
      constant := (1178973656139341068595392717808537926859568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree018.table
  base := (-1752067753266707949624845799327528815257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-2926484157588286395546006671040000000000000)
      constant := (6227271829611436454851320169097376689562908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203812607054815809951/100000000000000000000)
  centralHi := (6369143970462994061/3125000000000000000)
  directionLo := (2097214424646421591/1000000000000000000)
  directionHi := (209721442464642159101/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree019.table
  base := (-7499734905542494103626017658176247975973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-248989463307956896255257459257700000000000000)
      constant := (567556725440911876007086593294502211130448043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree019.table
  base := (-470203427559278238380144474181630632277/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-28201998722923835437592643130680000000000000)
      constant := (66469579756720139197298797228977259607160368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2097214424646421591/1000000000000000000)
  centralHi := (209721442464642159101/100000000000000000000)
  directionLo := (1683346089390485227/781250000000000000)
  directionHi := (215468299441982109057/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree020.table
  base := (-7960363779963459412556845785112880620171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-265508102144443500171044900294400000000000000)
      constant := (666062562663402040814866188556292577562417061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree020.table
  base := (-1994760293340190559847249483189277337391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-30065640027553093315271226222000000000000000)
      constant := (77851609432689175002282038648898758581784036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1683346089390485227/781250000000000000)
  centralHi := (215468299441982109057/100000000000000000000)
  directionLo := (110532905394037666001/50000000000000000000)
  directionHi := (221065810788075332003/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree021.table
  base := (-8365676082187228077037575004061516554099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (67320)
      previous := (49725)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-31336304553436678231870260147900000000000000)
      constant := (85875669767330033174314190623185995442788501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree021.table
  base := (-2095128365678024457807381230933589615851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-3547697925798039021438867701480000000000000)
      constant := (10019870403855106311794286745320770404076244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110532905394037666001/50000000000000000000)
  centralHi := (221065810788075332003/100000000000000000000)
  directionLo := (9061001916729392683/4000000000000000000)
  directionHi := (56631261979558704269/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree022.table
  base := (-8719481918234099127608273431086366068783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-298545379817416708002619782367800000000000000)
      constant := (887922930396787469263058719922699256695858753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree022.table
  base := (-4365634439221197223810731354158176845609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-33792922636811609070628392404640000000000000)
      constant := (103441896125027211442194723449749164049141982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9061001916729392683/4000000000000000000)
  centralHi := (56631261979558704269/25000000000000000000)
  directionLo := (231855778382441950787/100000000000000000000)
  directionHi := (57963944595610487697/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree023.table
  base := (-4512307332529344445467252153130825141187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-315064018653903311918407223404500000000000000)
      constant := (1011121943614722939306645031611471028539907034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree023.table
  base := (-9033975815785522635960273679052195921293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-35656563941440866948306975495960000000000000)
      constant := (117633856407679641616644869191465238408716907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231855778382441950787/100000000000000000000)
  centralHi := (57963944595610487697/25000000000000000000)
  directionLo := (118533335611018612321/50000000000000000000)
  directionHi := (237066671222037224643/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree024.table
  base := (-9283194101394990383478272769740882534099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (67320)
      previous := (49725)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-36842517498932212870466073826800000000000000)
      constant := (126936493962154740686358619149903964528808501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree024.table
  base := (-1161328141899734055781397513248936647049/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-4168911694007791647331728731920000000000000)
      constant := (14749948472734019645492826089848458472022712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118533335611018612321/50000000000000000000)
  centralHi := (237066671222037224643/100000000000000000000)
  directionLo := (242165462523595524813/100000000000000000000)
  directionHi := (121082731261797762407/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree025.table
  base := (-949681396542012430834438277864641774471/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (121176)
      previous := (89505)
      next := (0)
      square := (3888233449203769844793043813254000000000000)
      linear := (-69620259265375303949996421095580000000000000)
      constant := (256361025742761686267165197260683201402816722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree025.table
  base := (-9502709136853636172568347754335105806369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-39383846550699382703664141678600000000000000)
      constant := (148785054193053742863679515145974389797634231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242165462523595524813/100000000000000000000)
  centralHi := (121082731261797762407/50000000000000000000)
  directionLo := (247159090211621398907/100000000000000000000)
  directionHi := (61789772552905349727/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree026.table
  base := (-9666677285361680751974994279667059620999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-364619935163363123665769546514600000000000000)
      constant := (1429223831090190578448915751282273801332034409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree026.table
  base := (-302229706355433412319982754016959759727/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-41247487855328640581342724769920000000000000)
      constant := (165737489865424974737745836620380405278402336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247159090211621398907/100000000000000000000)
  centralHi := (61789772552905349727/25000000000000000000)
  directionLo := (50410760958035878867/20000000000000000000)
  directionHi := (7876681399693106073/3125000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree027.table
  base := (-4896847539044679324675981726861089628101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7480)
      previous := (5525)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-4705414493825305278784654167300000000000000)
      constant := (19563743540674522532685266616624290194957622) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree027.table
  base := (-2449349204691198808756724886754440641353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-4790125462217544273224589762360000000000000)
      constant := (20400515498446631614014261020631866618595932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50410760958035878867/20000000000000000000)
  centralHi := (7876681399693106073/3125000000000000000)
  directionLo := (256855261079416703439/100000000000000000000)
  directionHi := (3210690763492708793/1250000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree028.table
  base := (-4939279498809441898098270586521509535069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-397657212836336331497344428588000000000000000)
      constant := (1748107124898291546279559758628235966587139558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree028.table
  base := (-9881488679657048101828456288217670136337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-44974770464587156336699890952560000000000000)
      constant := (202384836082701593697085993963625839975387463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256855261079416703439/100000000000000000000)
  centralHi := (3210690763492708793/1250000000000000000)
  directionLo := (261568594787571494071/100000000000000000000)
  directionHi := (32696074348446436759/12500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree029.table
  base := (-620112201651794056932533370528148543617/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-414175851672822935413131869624700000000000000)
      constant := (1919543207995518235795773261183655131879514352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree029.table
  base := (-2481027968584490956547549405307215995283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-46838411769216414214378474043880000000000000)
      constant := (222076816380235341232567418775303724785075668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261568594787571494071/100000000000000000000)
  centralHi := (32696074348446436759/12500000000000000000)
  directionLo := (266198486874201126759/100000000000000000000)
  directionHi := (6654962171855028169/2500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree030.table
  base := (-1984760942315720060604111417154077329691/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (13464)
      previous := (9945)
      next := (0)
      square := (432025938800418871643671534806000000000000)
      linear := (-9570988677984656429531540236920000000000000)
      constant := (46643602007035423183314240766982244865473709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree030.table
  base := (-1985127002627781981916844177729421749463/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1479)
      previous := (1122)
      next := (0)
      square := (48002882088935430182630170534000000000000)
      linear := (-1082267846085459379823490158560000000000000)
      constant := (5392880480514423116916526631836197114405193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266198486874201126759/100000000000000000000)
  centralHi := (6654962171855028169/2500000000000000000)
  directionLo := (135374609001359340733/50000000000000000000)
  directionHi := (270749218002718681467/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree031.table
  base := (-988489336518145823402103512715648112917/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (121176)
      previous := (89505)
      next := (0)
      square := (3888233449203769844793043813254000000000000)
      linear := (-89442625869159228648941350339620000000000000)
      constant := (457271322152973673465127445183428786649451894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree031.table
  base := (-9886338177252112487626497755057200525539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-50565694378474929969735640226520000000000000)
      constant := (264192523320261710604377690636016221433073061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135374609001359340733/50000000000000000000)
  centralHi := (270749218002718681467/100000000000000000000)
  directionLo := (275224714885951225239/100000000000000000000)
  directionHi := (6880617872148780631/2500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree032.table
  base := (-9805294829927326390941327657422703930911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-463731768182282747160494192734800000000000000)
      constant := (2481721299998609881719826246403391923681304401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree032.table
  base := (-9806434378328714187184634169986039547879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-52429335683104187847414223317840000000000000)
      constant := (286614967428268730289486752310746311135966721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275224714885951225239/100000000000000000000)
  centralHi := (6880617872148780631/2500000000000000000)
  directionLo := (139814294976428106067/50000000000000000000)
  directionHi := (55925717990571242427/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree033.table
  base := (-4842593849727926464428898219585237581/5000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (13464)
      previous := (9945)
      next := (0)
      square := (432025938800418871643671534806000000000000)
      linear := (-10672231267083763357250702972700000000000000)
      constant := (59667821718206845839322785410493518820727600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree033.table
  base := (-484304287005617914499910981929147595853/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1479)
      previous := (1122)
      next := (0)
      square := (48002882088935430182630170534000000000000)
      linear := (-1206510599727409905002062364648000000000000)
      constant := (6887700716962508514239249136753905379193932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139814294976428106067/50000000000000000000)
  centralHi := (55925717990571242427/20000000000000000000)
  directionLo := (141982087738200319733/50000000000000000000)
  directionHi := (283964175476400639467/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree034.table
  base := (-9524708580250159390247875040637259235361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (35640)
      previous := (26325)
      next := (0)
      square := (1143598073295226424939130533310000000000000)
      linear := (-29221708579720938528945239694600000000000000)
      constant := (170373261465047030487463545572042494032907903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree034.table
  base := (-1905083146131788056122414192158393537527/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306000000000000000000000000000000000000000
      center := (783)
      previous := (594)
      next := (0)
      square := (25413290517671698331980678518000000000000)
      linear := (-660666097557208277679663405888000000000000)
      constant := (3931610549235068058857823513751765788758369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141982087738200319733/50000000000000000000)
  centralHi := (283964175476400639467/100000000000000000000)
  directionLo := (14411727653976943521/5000000000000000000)
  directionHi := (288234553079538870421/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree035.table
  base := (-9323962021008666522522143315980248209549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-513287684691742558907856515844900000000000000)
      constant := (3115599255377602916995756776354968369662667459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree035.table
  base := (-2331129606806740522483498392501163816759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-58020259596991961480449972591800000000000000)
      constant := (359335815998323072353641912923417891650439364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14411727653976943521/5000000000000000000)
  centralHi := (288234553079538870421/100000000000000000000)
  directionLo := (58488515872410702407/20000000000000000000)
  directionHi := (73110644840513378009/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree036.table
  base := (-4541514036917690016195071027730438648277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7480)
      previous := (5525)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-6540818808990483491649925393600000000000000)
      constant := (41269278207345871472935693925971806461295894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree036.table
  base := (-9083465544469468568507382299481404839131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-6653766766846802150903172853680000000000000)
      constant := (42821455963725241726298175995129874001491141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58488515872410702407/20000000000000000000)
  centralHi := (73110644840513378009/25000000000000000000)
  directionLo := (9268465882935802459/3125000000000000000)
  directionHi := (296590908253945678689/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree037.table
  base := (-8801968059936529279059639764835787238587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-546324962364715766739431397918300000000000000)
      constant := (3577980847689920912153288916719709056531916917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree037.table
  base := (-8802311772323322831868131545308003137833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-61747542206250477235807138774440000000000000)
      constant := (412358617462067313588531150442933883838496367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9268465882935802459/3125000000000000000)
  centralHi := (296590908253945678689/100000000000000000000)
  directionLo := (150341005296184812283/50000000000000000000)
  directionHi := (300682010592369624567/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree038.table
  base := (-4240414485454119302946684741644998106293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-562843601201202370655218838955000000000000000)
      constant := (3821106094036045210778471684788664478659574326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree038.table
  base := (-13569758134284462528381927633202048789/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (13311)
      previous := (10098)
      next := (0)
      square := (432025938800418871643671534806000000000000)
      linear := (-12722236702175947022697144373152000000000000)
      constant := (88046449768411652064881196983151183887476375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150341005296184812283/50000000000000000000)
  centralHi := (300682010592369624567/100000000000000000000)
  directionLo := (60943638266463657297/20000000000000000000)
  directionHi := (152359095666159143243/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree039.table
  base := (-1014955853915640040403272109827293883151/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (67320)
      previous := (49725)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-64373582226409886063445142221300000000000000)
      constant := (452465158948235709512301234441463668879393992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree039.table
  base := (-1014982321594339402944164921494137532531/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-7274980535056554776796033884120000000000000)
      constant := (52112657220958859925618798658585554024788328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60943638266463657297/20000000000000000000)
  centralHi := (152359095666159143243/50000000000000000000)
  directionLo := (308701604731508954121/100000000000000000000)
  directionHi := (154350802365754477061/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree040.table
  base := (-964806158682535233373993368554084939269/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-595880878874175578486793721028400000000000000)
      constant := (4331221210433904264682230878364139405253215832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree040.table
  base := (-1929653825633677644181351689059447630787/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-67338466120138250868842888048400000000000000)
      constant := (498703552661768435778930924387025506849292052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308701604731508954121/100000000000000000000)
  centralHi := (154350802365754477061/50000000000000000000)
  directionLo := (312634267793500601859/100000000000000000000)
  directionHi := (15631713389675030093/5000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree041.table
  base := (-727725748363631834857572030715972114083/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (121176)
      previous := (89505)
      next := (0)
      square := (3888233449203769844793043813254000000000000)
      linear := (-122479903542132436480516232413020000000000000)
      constant := (919641987500772043806123714843689617562862106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree041.table
  base := (-7277387596818798384240746725685547847977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-69202107424767508746521471139720000000000000)
      constant := (529301113551668138210583681029811890047411823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312634267793500601859/100000000000000000000)
  centralHi := (15631713389675030093/5000000000000000000)
  directionLo := (39564759025897123149/12500000000000000000)
  directionHi := (316518072207176985193/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree042.table
  base := (-271843509876236657076778973138201188857/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (13464)
      previous := (9945)
      next := (0)
      square := (432025938800418871643671534806000000000000)
      linear := (-13975959034381084140408191180040000000000000)
      constant := (108292271795735531259037809982137693538914715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree042.table
  base := (-6796189652274549485242966552535837341213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-7896194303266307402688894914560000000000000)
      constant := (62311840081421832763657209257837143008389443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39564759025897123149/12500000000000000000)
  centralHi := (316518072207176985193/100000000000000000000)
  directionLo := (20022174686448932451/6250000000000000000)
  directionHi := (320354794983182919217/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree043.table
  base := (-98046133731653433393906906943819392837/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-645436795383635390234156044138500000000000000)
      constant := (5156047797744496515804390928849286437317034688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree043.table
  base := (-3137516163767709422711134994630486961351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-72929390034026024501878637322360000000000000)
      constant := (593219865961847889400164311299012206827052098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20022174686448932451/6250000000000000000)
  centralHi := (320354794983182919217/100000000000000000000)
  directionLo := (162073053978511968017/50000000000000000000)
  directionHi := (64829221591404787207/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree044.table
  base := (-5713861527319799035568294438410103855261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-661955434220121994149943485175200000000000000)
      constant := (5446896413401165496843653544327257878852195251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree044.table
  base := (-2856961967494687589684320704355352998797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-74793031338655282379557220413680000000000000)
      constant := (626541007618301215165683415611463453700258006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162073053978511968017/50000000000000000000)
  centralHi := (64829221591404787207/20000000000000000000)
  directionLo := (327893586303020072431/100000000000000000000)
  directionHi := (20493349143938754527/6250000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree045.table
  base := (-255641102201052071982960746658939190159/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1496)
      previous := (1105)
      next := (0)
      square := (48002882088935430182630170534000000000000)
      linear := (-1675244624831132340903039323980000000000000)
      constant := (14186908406783616228486591848612266296176196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree045.table
  base := (-1278217711092206039110464974011138194471/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-8517408071476060028581755945000000000000000)
      constant := (73418885459386942780385267873043124247191524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327893586303020072431/100000000000000000000)
  centralHi := (20493349143938754527/6250000000000000000)
  directionLo := (331598716182112998003/100000000000000000000)
  directionHi := (82899679045528249501/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree046.table
  base := (-4471839801544936627568963427430992056299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-694992711893095201981518367248600000000000000)
      constant := (6052452138524660085910320474862267906954096709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree046.table
  base := (-2235938971470424476973128443233137593809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-78520313947913798134914386596320000000000000)
      constant := (695906737798610015629347730973821218237005582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331598716182112998003/100000000000000000000)
  centralHi := (82899679045528249501/25000000000000000000)
  directionLo := (335262901628848557627/100000000000000000000)
  directionHi := (83815725407212139407/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree047.table
  base := (-1895459594872660535411798874666274889649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-711511350729581805897305808285300000000000000)
      constant := (6367159011970963579001452385150624342216413118) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree047.table
  base := (-3790948986409567585380344499240322182817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-80383955252543056012592969687640000000000000)
      constant := (731951303842097396030214745938555922002492983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335262901628848557627/100000000000000000000)
  centralHi := (83815725407212139407/25000000000000000000)
  directionLo := (67777494153609556717/20000000000000000000)
  directionHi := (169443735384023891793/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree048.table
  base := (-3070063599302990047990361661743588275487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (67320)
      previous := (49725)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-80892221062896489979232583258000000000000000)
      constant := (743313160634869812792720535589804926895458313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree048.table
  base := (-3070086866514093639547707679380820383991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-9138621839685812654474616975440000000000000)
      constant := (85433739971503465753510036812178942909026601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67777494153609556717/20000000000000000000)
  centralHi := (169443735384023891793/50000000000000000000)
  directionLo := (85618420359805567813/25000000000000000000)
  directionHi := (342473681439222271253/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree049.table
  base := (-2309275654343142086946237410693183667639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-744548628402555013728880690358700000000000000)
      constant := (7020430378325107521970345502937833263524238649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree049.table
  base := (-577323453779911535966492312342977497499/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-84111237861801571767950135870280000000000000)
      constant := (806763799697829968193161250125703662116020404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85618420359805567813/25000000000000000000)
  centralHi := (342473681439222271253/100000000000000000000)
  directionLo := (346022726296269958469/100000000000000000000)
  directionHi := (34602272629626995847/10000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree050.table
  base := (-754278695345806939508116753582855488603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-761067267239041617644668131395400000000000000)
      constant := (7358994762148154188401807308805757871734584746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree050.table
  base := (-1508571559889362677381976108445463703297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-85974879166430829645628718961600000000000000)
      constant := (845531719211341904421826653601933348907724503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346022726296269958469/100000000000000000000)
  centralHi := (34602272629626995847/10000000000000000000)
  directionLo := (21845983590066891573/6250000000000000000)
  directionHi := (349535737441070265169/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree051.table
  base := (-534328313990545898667070404575965703/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306000000000000000000000000000000000000000
      center := (792)
      previous := (585)
      next := (0)
      square := (25413290517671698331980678518000000000000)
      linear := (-1016452164804612054327392905140000000000000)
      constant := (10072564130849464412845234530774969311860250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree051.table
  base := (-33396072151841776456067802569333958727/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34000000000000000000000000000000000000000
      center := (87)
      previous := (66)
      next := (0)
      square := (2823698946407966481331186502000000000000)
      linear := (-114821595387006650357264447128000000000000)
      constant := (1157133875546365290096510959273285290806564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21845983590066891573/6250000000000000000)
  centralHi := (349535737441070265169/100000000000000000000)
  directionLo := (7060275812840239623/2000000000000000000)
  directionHi := (353013790642011981151/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree052.table
  base := (212664103103035607524504854254069877269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-794104544912014825476243013468800000000000000)
      constant := (8059980743219390973545044841449233521756990021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree052.table
  base := (42531097614793676231984217631346045151/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (13311)
      previous := (10098)
      next := (0)
      square := (432025938800418871643671534806000000000000)
      linear := (-17940432355137869080197177028848000000000000)
      constant := (185158176743703783548177732662955131063437751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7060275812840239623/2000000000000000000)
  centralHi := (353013790642011981151/100000000000000000000)
  directionLo := (4455723864775153631/1250000000000000000)
  directionHi := (356457909182012290481/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree053.table
  base := (1133165125625949351721487140682024242829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-810623183748501429392030454505500000000000000)
      constant := (8422402288789399654083729043642975505500384061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree053.table
  base := (1133158411797762779139216281087071023881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-91565803080318603278664468235560000000000000)
      constant := (967282123850890927273486807899387471733114481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4455723864775153631/1250000000000000000)
  centralHi := (356457909182012290481/100000000000000000000)
  directionLo := (71973813475008027583/20000000000000000000)
  directionHi := (89967266843760034479/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree054.table
  base := (1046795954896577619252896137794724539537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7480)
      previous := (5525)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-10211627439320839917380467846200000000000000)
      constant := (108552792332040166494870240158645350783852386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree054.table
  base := (32712291866406484197067343105061346199/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-10381049376105317906260339036320000000000000)
      constant := (112186792611428556225646460277751214659296704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71973813475008027583/20000000000000000000)
  centralHi := (89967266843760034479/25000000000000000000)
  directionLo := (18162409689269664361/5000000000000000000)
  directionHi := (363248193785393287221/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree055.table
  base := (1546971924148631683575997765034684912887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-843660461421474637223605336578900000000000000)
      constant := (9171102399320493779361244601592143878251543566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree055.table
  base := (24751518200290992082687615610329059543/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (13311)
      previous := (10098)
      next := (0)
      square := (432025938800418871643671534806000000000000)
      linear := (-19058617137915423806804326883640000000000000)
      constant := (210597582266463169412770194684861647096783575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18162409689269664361/5000000000000000000)
  centralHi := (363248193785393287221/100000000000000000000)
  directionLo := (22912260886242088697/6250000000000000000)
  directionHi := (366596174179873419153/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree056.table
  base := (4134220455619152721555669748990489670673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-860179100257961241139392777615600000000000000)
      constant := (9557380938699603430048005954594118372700784257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree056.table
  base := (4134217284506494344969655748224270347729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-97156726994206376911700217509520000000000000)
      constant := (1097202456262322501728800695259051327174443129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22912260886242088697/6250000000000000000)
  centralHi := (366596174179873419153/100000000000000000000)
  directionLo := (369913854239456063597/100000000000000000000)
  directionHi := (184956927119728031799/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree057.table
  base := (5214421340263699170517146307510018732651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (67320)
      previous := (49725)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-97410859899383093895020024294700000000000000)
      constant := (1105734643096452564150835607668583558723625251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree057.table
  base := (521441887227279943027820855131617556601/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1479)
      previous := (1122)
      next := (0)
      square := (48002882088935430182630170534000000000000)
      linear := (-2200452628863014106430640013352000000000000)
      constant := (25384994831555859630828744878130074947715378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (369913854239456063597/100000000000000000000)
  centralHi := (184956927119728031799/50000000000000000000)
  directionLo := (373202042053977784699/100000000000000000000)
  directionHi := (3732020420539777847/1000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree058.table
  base := (6334546183454311275810681722003615513461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-893216377930934448970967659689000000000000000)
      constant := (10353794939363661492312361715653382635554608549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree058.table
  base := (791818032908892145263014949935593526397/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-100884009603464892667057383692160000000000000)
      constant := (1188354844089947532416415812725139830097268776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373202042053977784699/100000000000000000000)
  centralHi := (3732020420539777847/1000000000000000000)
  directionLo := (376461510420691558829/100000000000000000000)
  directionHi := (37646151042069155883/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree059.table
  base := (1498918944555573214989937079440267792489/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (121176)
      previous := (89505)
      next := (0)
      square := (3888233449203769844793043813254000000000000)
      linear := (-181947003353484210577351020145140000000000000)
      constant := (2152786077408707975896736219051567228754375001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree059.table
  base := (936824153656162545134199669747307071621/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-102747650908094150544735966783480000000000000)
      constant := (1235292685678440057942616343105021965546289768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376461510420691558829/100000000000000000000)
  centralHi := (37646151042069155883/10000000000000000000)
  directionLo := (94923249741303472233/25000000000000000000)
  directionHi := (379692998965213888933/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree060.table
  base := (4347283369812125062305096231636399971547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (67320)
      previous := (49725)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-102917072844878628533615837973600000000000000)
      constant := (1242446458421140454808523101576972552651987494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree060.table
  base := (4347282789140640362887427391967541074107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-11623476912524823158046061097200000000000000)
      constant := (142570921298476856930435894728557238740833846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94923249741303472233/25000000000000000000)
  centralHi := (379692998965213888933/100000000000000000000)
  directionLo := (382897216101354504903/100000000000000000000)
  directionHi := (47862152012669313113/12500000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree061.table
  base := (4967231024767432903096570895417071034093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-942772294440394260718329982799100000000000000)
      constant := (11608058151285842822037656750480386431674166074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree061.table
  base := (620903821671435326851773024316520066093/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-106474933517352666300093132966120000000000000)
      constant := (1331891661687916177728202600488076299070526288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (382897216101354504903/100000000000000000000)
  centralHi := (47862152012669313113/12500000000000000000)
  directionLo := (77214968168907983489/20000000000000000000)
  directionHi := (193037420422269958723/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree062.table
  base := (2242856098956289657701356772546622806381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (121176)
      previous := (89505)
      next := (0)
      square := (3888233449203769844793043813254000000000000)
      linear := (-191858186655376172926823484767160000000000000)
      constant := (2408410091967603022866631987934743893274572829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree062.table
  base := (140178497414579455769402277712138746277/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (13311)
      previous := (10098)
      next := (0)
      square := (432025938800418871643671534806000000000000)
      linear := (-21667714964396384835554343211488000000000000)
      constant := (276310559063071038547846163891124366065063632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77214968168907983489/20000000000000000000)
  centralHi := (193037420422269958723/50000000000000000000)
  directionLo := (97306631122995121109/25000000000000000000)
  directionHi := (389226524491980484437/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree063.table
  base := (6267010969327564613458972360319106904249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7480)
      previous := (5525)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-12047031754486018130245739072500000000000000)
      constant := (154123395657364976186218512501014443790655922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree063.table
  base := (1253402139352771219974301516172940438421/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1479)
      previous := (1122)
      next := (0)
      square := (48002882088935430182630170534000000000000)
      linear := (-2448938136146915156787784425528000000000000)
      constant := (31824926494356066753068830562291959573407338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97306631122995121109/25000000000000000000)
  centralHi := (389226524491980484437/100000000000000000000)
  directionLo := (392352892181357241107/100000000000000000000)
  directionHi := (98088223045339310277/25000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree064.table
  base := (13893686261067196908796591410257987629783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-992328210949854072465692305909200000000000000)
      constant := (12933891913700330039808319027778729232425590247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree064.table
  base := (13893685837630478652264555216933014244229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-112065857431240439933128882240080000000000000)
      constant := (1483598352193298374761975920501962770049239629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392352892181357241107/100000000000000000000)
  centralHi := (98088223045339310277/25000000000000000000)
  directionLo := (395454544338594238251/100000000000000000000)
  directionHi := (98863636084648559563/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree065.table
  base := (3823318338789027308427803438010221034421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-1008846849786340676381479746945900000000000000)
      constant := (13391741053697794181478017263470275056779044756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree065.table
  base := (15293273026324332270363463969363933788533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-113929498735869697810807465331400000000000000)
      constant := (1535982774899291313810559021839315591783974333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (395454544338594238251/100000000000000000000)
  centralHi := (98863636084648559563/25000000000000000000)
  directionLo := (24908253626513310543/6250000000000000000)
  directionHi := (398532058024212968689/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree066.table
  base := (8366391562333328928880745042223631849947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (67320)
      previous := (49725)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-113929498735869697810807465331400000000000000)
      constant := (1539726940665079702663381287764647332883424294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree066.table
  base := (16732782869362991537759040204699932684757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-12865904448944328409831783158080000000000000)
      constant := (176586106681030138090000063939638280545894773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24908253626513310543/6250000000000000000)
  centralHi := (398532058024212968689/100000000000000000000)
  directionLo := (200792994093409611593/50000000000000000000)
  directionHi := (401585988186819223187/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree067.table
  base := (18212215481921847858394469569689173729809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-1041884127459313884213054629019300000000000000)
      constant := (14331296148511668693143519980851603867841098881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree067.table
  base := (18212215283750245808863171107704880268673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-117656781345128213566164631514040000000000000)
      constant := (1643474907667365017871125899921820393578818473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200792994093409611593/50000000000000000000)
  centralHi := (401585988186819223187/100000000000000000000)
  directionLo := (80923373766286725391/20000000000000000000)
  directionHi := (101154217207858406739/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree068.table
  base := (19731570346249946215919825584221502376617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (35640)
      previous := (26325)
      next := (0)
      square := (1143598073295226424939130533310000000000000)
      linear := (-62258986252694146360520121768000000000000000)
      constant := (871353064669835511219961857673473008772601609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree068.table
  base := (19731570192459329937638826406385855578741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3915)
      previous := (2970)
      next := (0)
      square := (127066452588358491659903392590000000000000)
      linear := (-7030613097044557143755483212080000000000000)
      constant := (99916624547836824873476039970417035903547373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80923373766286725391/20000000000000000000)
  centralHi := (101154217207858406739/25000000000000000000)
  directionLo := (407625214109631619903/100000000000000000000)
  directionHi := (6369143970462994061/1562500000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree069.table
  base := (1064542382138062571391609551632231133679/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (13464)
      previous := (9945)
      next := (0)
      square := (432025938800418871643671534806000000000000)
      linear := (-23887142336273046489880655802060000000000000)
      constant := (340059118152427317650795072229731732714796316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree069.table
  base := (2129084752343798719989853426443668673077/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1479)
      previous := (1122)
      next := (0)
      square := (48002882088935430182630170534000000000000)
      linear := (-2697423643430816207144928837704000000000000)
      constant := (38991068641765474177873095554140440493038506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (407625214109631619903/100000000000000000000)
  centralHi := (6369143970462994061/1562500000000000000)
  directionLo := (102652879834448774359/25000000000000000000)
  directionHi := (410611519337795097437/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree070.table
  base := (2861255912674216798461189010705023092683/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-1091440043968773695960416952129400000000000000)
      constant := (15800270799287663464430097952427751084612930776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree070.table
  base := (22890047208832319104117212263356475163977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-123247705259015987199200380788000000000000000)
      constant := (1811521322189537973360259021868990191901504177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102652879834448774359/25000000000000000000)
  centralHi := (410611519337795097437/100000000000000000000)
  directionLo := (103394065487296565827/25000000000000000000)
  directionHi := (413576261949186263309/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree071.table
  base := (24529169256165550866553437481792646160913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-1107958682805260299876204393166100000000000000)
      constant := (16305833545127937209617092822040034053980812417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree071.table
  base := (3066146148047294011391202812290451074103/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-125111346563645245076878963879320000000000000)
      constant := (1869352317076350333689613061504659705949935224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103394065487296565827/25000000000000000000)
  centralHi := (413576261949186263309/100000000000000000000)
  directionLo := (104129975596256440553/25000000000000000000)
  directionHi := (416519902385025762213/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree072.table
  base := (13104106722293436066708158594541067167229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7480)
      previous := (5525)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-13882436069651196343111010298800000000000000)
      constant := (207646278431076865791143268883644736822658362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree072.table
  base := (5241642677784465375506261390258284474849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1479)
      previous := (1122)
      next := (0)
      square := (48002882088935430182630170534000000000000)
      linear := (-2821666397072766732323501043792000000000000)
      constant := (42846468297351610913249253856408644213231361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104129975596256440553/25000000000000000000)
  centralHi := (416519902385025762213/100000000000000000000)
  directionLo := (419442884929284318201/100000000000000000000)
  directionHi := (209721442464642159101/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree073.table
  base := (44683487691511283062388088867394013881/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (121176)
      previous := (89505)
      next := (0)
      square := (3888233449203769844793043813254000000000000)
      linear := (-228199192095646701541555855047900000000000000)
      constant := (3468163164252711486338376463220453308867541125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree073.table
  base := (3490897470504990974776010869729475687427/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-128838629172903760832236130061960000000000000)
      constant := (1987737590950992800535107129264010930103981016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419442884929284318201/100000000000000000000)
  centralHi := (209721442464642159101/50000000000000000000)
  directionLo := (422345638491473357869/100000000000000000000)
  directionHi := (42234563849147335787/10000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree074.table
  base := (742151707179540845112623211312714581243/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (121176)
      previous := (89505)
      next := (0)
      square := (3888233449203769844793043813254000000000000)
      linear := (-231502919862944022324713343255240000000000000)
      constant := (3574047069767427414997780878587154685058539096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree074.table
  base := (1187442730149267871971024148520806489371/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (13311)
      previous := (10098)
      next := (0)
      square := (432025938800418871643671534806000000000000)
      linear := (-26140454095506603741982942630656000000000000)
      constant := (409658373928241334321626392285977088394269855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (422345638491473357869/100000000000000000000)
  centralHi := (42234563849147335787/10000000000000000000)
  directionLo := (85045715468267949239/20000000000000000000)
  directionHi := (106307144335334936549/25000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree075.table
  base := (31484878830100207808436607346146439666787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (67320)
      previous := (49725)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-130448137572356301726594906368100000000000000)
      constant := (2045289681595932659318356507776076889573312987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree075.table
  base := (7871219701044309543129800923523229003599/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-14729545753573586287510366249400000000000000)
      constant := (234417101034608583897580511802592852728160444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85045715468267949239/20000000000000000000)
  centralHi := (106307144335334936549/25000000000000000000)
  directionLo := (85618420359805567813/20000000000000000000)
  directionHi := (214046050899513919533/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree076.table
  base := (1332944455344844437381322950944492077033/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (121176)
      previous := (89505)
      next := (0)
      square := (3888233449203769844793043813254000000000000)
      linear := (-238110375397538663891028319669920000000000000)
      constant := (3790586235323470926371703564973298075156327485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree076.table
  base := (8330902840883727768160950663493615962621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-134429553086791534465271879335920000000000000)
      constant := (2172123709826964443106772549517707580475108884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85618420359805567813/20000000000000000000)
  centralHi := (214046050899513919533/50000000000000000000)
  directionLo := (430936598883964218113/100000000000000000000)
  directionHi := (215468299441982109057/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree077.table
  base := (35202265897337789607959754858801428482407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-1207070515824179923370929039386300000000000000)
      constant := (19506207474419052156335529641124432639344665463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree077.table
  base := (3520226588177682882455171903548628768849/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (13311)
      previous := (10098)
      next := (0)
      square := (432025938800418871643671534806000000000000)
      linear := (-27258638878284158468590092485448000000000000)
      constant := (447080254211509140490369344316555966855552498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430936598883964218113/100000000000000000000)
  centralHi := (215468299441982109057/50000000000000000000)
  directionLo := (433762442925442920127/100000000000000000000)
  directionHi := (6777538170710045627/1562500000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree078.table
  base := (37120842322604572878094252874093843910261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (67320)
      previous := (49725)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-135954350517851836365190720047000000000000000)
      constant := (2229715114069971110668124923372518088010588861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree078.table
  base := (37120842310551366937385368417673996306317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-15350759521783338913403227279840000000000000)
      constant := (255509621430828717534747393926627784932525613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (433762442925442920127/100000000000000000000)
  centralHi := (6777538170710045627/1562500000000000000)
  directionLo := (17462799845505534877/4000000000000000000)
  directionHi := (218284998068819185963/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree079.table
  base := (2442458788275115835881007301628162275643/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-1240107793497153131202503921459700000000000000)
      constant := (20636616832148736161947297715245768411368431792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree079.table
  base := (39079340603067200939239596168955137456101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-140020477000679308098307628609880000000000000)
      constant := (2364679675164998474237986713591572312523318701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17462799845505534877/4000000000000000000)
  centralHi := (218284998068819185963/50000000000000000000)
  directionLo := (43935960916154666387/10000000000000000000)
  directionHi := (439359609161546663871/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree080.table
  base := (41077760721222397283827138753090306106803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-1256626432333639735118291362496400000000000000)
      constant := (21213749889910761817829706545631090975654151427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree080.table
  base := (20538880356997142175210744308042199522161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-141884118305308565975986211701200000000000000)
      constant := (2430680517802262300833945957874435521914281522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43935960916154666387/10000000000000000000)
  centralHi := (439359609161546663871/100000000000000000000)
  directionLo := (110532905394037666001/25000000000000000000)
  directionHi := (88426324315230132801/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree081.table
  base := (43116102604974327621295366869477187473657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7480)
      previous := (5525)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-15717840384816374555976281525100000000000000)
      constant := (269121422208440373028336607434028907179886873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree081.table
  base := (4311610259937823830072306428693649106773/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1479)
      previous := (1122)
      next := (0)
      square := (48002882088935430182630170534000000000000)
      linear := (-3194394657998618307859217662056000000000000)
      constant := (55501980459442768847982073741760929183714794) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110532905394037666001/25000000000000000000)
  centralHi := (88426324315230132801/20000000000000000000)
  directionLo := (27805397648807407377/6250000000000000000)
  directionHi := (444886362380918518033/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree082.table
  base := (2259718311044867021096356243721082871381/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (121176)
      previous := (89505)
      next := (0)
      square := (3888233449203769844793043813254000000000000)
      linear := (-257932742001322588589973248913960000000000000)
      constant := (4478374551613297079767453699259267315744631316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree082.table
  base := (2824647888535339702373139301528317235159/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-145611400914567081731343377883840000000000000)
      constant := (2565405483672043280950523975683282450058376944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27805397648807407377/6250000000000000000)
  centralHi := (444886362380918518033/100000000000000000000)
  directionLo := (447624150451576291789/100000000000000000000)
  directionHi := (44762415045157629179/10000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree083.table
  base := (47312551527489493077832979311562572643467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-1306182348843099546865653685606500000000000000)
      constant := (22992862566487688393947632680271118263010919003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree083.table
  base := (23656275762068339591272717140355335621527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-147475042219196339609021960975160000000000000)
      constant := (2634129606685887020464952687574008455903183454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447624150451576291789/100000000000000000000)
  centralHi := (44762415045157629179/10000000000000000000)
  directionLo := (450345294970942117803/100000000000000000000)
  directionHi := (112586323742735529451/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree084.table
  base := (9894131696888500565400864021990203521509/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (13464)
      previous := (9945)
      next := (0)
      square := (432025938800418871643671534806000000000000)
      linear := (-29393355281768581128476469480960000000000000)
      constant := (524484547182304502432233293353996519359444909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree084.table
  base := (9894131696369571858083361819252228989701/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1479)
      previous := (1122)
      next := (0)
      square := (48002882088935430182630170534000000000000)
      linear := (-3318637411640568833037789868144000000000000)
      constant := (60083588658039575208825612358339894178023589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (450345294970942117803/100000000000000000000)
  centralHi := (112586323742735529451/25000000000000000000)
  directionLo := (453050095836469634151/100000000000000000000)
  directionHi := (56631261979558704269/12500000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree085.table
  base := (516686870525839536110838146250132957891/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2754000000000000000000000000000000000000000
      center := (7128)
      previous := (5265)
      next := (0)
      square := (228719614659045284987826106662000000000000)
      linear := (-15755525017836150055261512560940000000000000)
      constant := (284925869732912246562773861863478661660318140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree085.table
  base := (12917171762644079148897237077810773540917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3915)
      previous := (2970)
      next := (0)
      square := (127066452588358491659903392590000000000000)
      linear := (-8894254401673815021434066303400000000000000)
      constant := (163194184255762755104504090178620193407041204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (453050095836469634151/100000000000000000000)
  centralHi := (56631261979558704269/12500000000000000000)
  directionLo := (45573884404602135727/10000000000000000000)
  directionHi := (455738844046021357271/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree086.table
  base := (26953318596912581716155049620118211042027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-1355738265352559358613016008716600000000000000)
      constant := (24843545477877585482217877091769694404565620086) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree086.table
  base := (53906637192271942025864601160130292660189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-153065966133084113242057710249120000000000000)
      constant := (2845748534795476543906418569066618891209151589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45573884404602135727/10000000000000000000)
  centralHi := (455738844046021357271/100000000000000000000)
  directionLo := (91682364412655334293/20000000000000000000)
  directionHi := (229205911031638335733/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree087.table
  base := (14046127217778434184400515496919876121621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (67320)
      previous := (49725)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-152472989354338440280978161083700000000000000)
      constant := (2830704919341830739454968772332704391169344884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree087.table
  base := (11236901773982447438951930283795934402587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1479)
      previous := (1122)
      next := (0)
      square := (48002882088935430182630170534000000000000)
      linear := (-3442880165282519358216362074232000000000000)
      constant := (64846748819066988610743432842601025042347643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91682364412655334293/20000000000000000000)
  centralHi := (229205911031638335733/50000000000000000000)
  directionLo := (461069304164073243837/100000000000000000000)
  directionHi := (230534652082036621919/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree088.table
  base := (29251151024195018108750886347033092750693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-1388775543025532566444590890790000000000000000)
      constant := (26117095315050094426689203148643395336401944874) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree088.table
  base := (29251151023730366689040933213439552803699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-156793248742342628997414876431760000000000000)
      constant := (2991366618441849812356053262436792553684842198) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (461069304164073243837/100000000000000000000)
  centralHi := (230534652082036621919/50000000000000000000)
  directionLo := (231855778382441950787/50000000000000000000)
  directionHi := (18548462270595356063/4000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree089.table
  base := (30430008345273485138977629830899529193559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-1405294181862019170360378331826700000000000000)
      constant := (26765798599976616889876120261247804157784045262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree089.table
  base := (30430008344914145083131632730826249544399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-158656890046971886875093459523080000000000000)
      constant := (3065537299455715664318928604767478150129963598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231855778382441950787/50000000000000000000)
  centralHi := (18548462270595356063/4000000000000000000)
  directionLo := (93267767746908492437/20000000000000000000)
  directionHi := (233169419367271231093/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree090.table
  base := (6325765276339261747509636014540816186669/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1496)
      previous := (1105)
      next := (0)
      square := (48002882088935430182630170534000000000000)
      linear := (-3510648939996310553768310550280000000000000)
      constant := (67709763279149741618706190827404591755894682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree090.table
  base := (31628826381418446227244441382429448087531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-17835614594622349416974671401600000000000000)
      constant := (348957304423412780676050753219044220994592918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93267767746908492437/20000000000000000000)
  centralHi := (233169419367271231093/50000000000000000000)
  directionLo := (468951401690250902789/100000000000000000000)
  directionHi := (46895140169025090279/10000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree091.table
  base := (32847605116807652972959106213924439748959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-1438331459534992378191953213900100000000000000)
      constant := (28087061898507386897147736594262264420166762462) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree091.table
  base := (65695210233185639491876411748685578965753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-162384172656230402630450625705720000000000000)
      constant := (3216601939420232254799592905613651190889923553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468951401690250902789/100000000000000000000)
  centralHi := (46895140169025090279/10000000000000000000)
  directionLo := (471549490278825891/100000000000000000)
  directionHi := (471549490278825891001/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree092.table
  base := (68172689068750840875070357348491487356377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-1454850098371478982107740654936800000000000000)
      constant := (28759621910571887178158769290246837227525429193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree092.table
  base := (2130396533388083682746613291926734646699/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-164247813960859660508129208797040000000000000)
      constant := (3293495898199849675691517460081325978114051168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471549490278825891/100000000000000000)
  centralHi := (471549490278825891001/100000000000000000000)
  directionLo := (118533335611018612321/25000000000000000000)
  directionHi := (94826668488814889857/20000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree093.table
  base := (70690089237151631335674705361191559796247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (67320)
      previous := (49725)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-163485415245329509558169788441500000000000000)
      constant := (3271126018167589749177979574985209247030038447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree093.table
  base := (70690089236894875330016026197602513133143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-18456828362832102042867532432040000000000000)
      constant := (374588624007474300436387758975227126295478327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118533335611018612321/25000000000000000000)
  centralHi := (94826668488814889857/20000000000000000000)
  directionLo := (95340637936225164711/20000000000000000000)
  directionHi := (119175797420281455889/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree094.table
  base := (73247410707957513284351736446411965309921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-1487887376044452189939315537010200000000000000)
      constant := (30128598656594243010385406063985057695939940689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree094.table
  base := (4577963169234941757858169735678999127593/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-167975096570118176263486374979680000000000000)
      constant := (3450007092942235058431148362583537227693910288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95340637936225164711/20000000000000000000)
  centralHi := (119175797420281455889/25000000000000000000)
  directionLo := (95851851455697793851/20000000000000000000)
  directionHi := (59907407159811121157/12500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree095.table
  base := (1516893069021362020684740995106071397499/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (121176)
      previous := (89505)
      next := (0)
      square := (3888233449203769844793043813254000000000000)
      linear := (-300881202976187758771020595609380000000000000)
      constant := (6165003077825014610593146039626130253440540910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree095.table
  base := (75844653450914741053826399744065328296413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-169838737874747434141164958071000000000000000)
      constant := (3529624328746467703216167680981313918898970213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95851851455697793851/20000000000000000000)
  centralHi := (59907407159811121157/12500000000000000000)
  directionLo := (60225220568568999929/12500000000000000000)
  directionHi := (481801764548551999433/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree096.table
  base := (39240908718558263721648715487057215997161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (67320)
      previous := (49725)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-168991628190825044196765602120400000000000000)
      constant := (3503264928934816541934992562603671637617231522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree096.table
  base := (4905113589812376409965427456924684613153/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7395)
      previous := (5610)
      next := (0)
      square := (240014410444677150913150852670000000000000)
      linear := (-19078042131041854668760393462480000000000000)
      constant := (401127702600399023152040745426099741651219472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60225220568568999929/12500000000000000000)
  centralHi := (481801764548551999433/100000000000000000000)
  directionLo := (484330925047191049627/100000000000000000000)
  directionHi := (121082731261797762407/25000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree097.table
  base := (40579451318722227539972197806875695668863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-1537443292553912001686677860120300000000000000)
      constant := (32241705569788207462796959826487056319824827934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree097.table
  base := (2536215707417277916334384527057965496163/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-173566020484005949896522124253640000000000000)
      constant := (3691582076839071267636707057441168584176638816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell023.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484330925047191049627/100000000000000000000)
  centralHi := (121082731261797762407/25000000000000000000)
  directionLo := (121711736695777733711/25000000000000000000)
  directionHi := (97369389356622186969/20000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree098.table
  base := (83875909024078258100819990758813146634003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (605880)
      previous := (447525)
      next := (0)
      square := (19441167246018849223965219066270000000000000)
      linear := (-1553961931390398605602465301157000000000000000)
      constant := (32961979016594814201744644167496056949555376227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree098.table
  base := (83875909024007521103432991377004389915839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (66555)
      previous := (50490)
      next := (0)
      square := (2160129694002094358218357674030000000000000)
      linear := (-175429661788635207774200707344960000000000000)
      constant := (3773922588980153145364548679911268418171097239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell023.Kernel098
