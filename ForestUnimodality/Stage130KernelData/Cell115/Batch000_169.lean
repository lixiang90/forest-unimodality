import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell115.Parameters
import ForestUnimodality.BinomialMassData.Q4583_8778.Batch000_049
import ForestUnimodality.BinomialMassData.Q4583_8778.Batch050_099
import ForestUnimodality.BinomialMassData.Q4583_8778.Batch100_149
import ForestUnimodality.BinomialMassData.Q4583_8778.Batch150_199
import ForestUnimodality.BinomialMassData.Q2294_4389.Batch000_049
import ForestUnimodality.BinomialMassData.Q2294_4389.Batch050_099
import ForestUnimodality.BinomialMassData.Q2294_4389.Batch100_149
import ForestUnimodality.BinomialMassData.Q2294_4389.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree000.table
  base := (729333582637518877300664147/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (705440239366169064005873680000000000000)
      linear := (-38922876886991024381057258000000000000)
      constant := (729333582637518877300664147000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree000.table
  base := (729333582637518877300664147/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (705440239366169064005873680000000000000)
      linear := (-38922876886991024381057258000000000000)
      constant := (729333582637518877300664147000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree001.table
  base := (100342536391911292875716723373236425964661/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-1358142184345190414112604372939998000000000000)
      constant := (703256151245111435260622644813440611999999817884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree001.table
  base := (401013588680811876170953560621163976813759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-1359549537622725921395296090931598000000000000)
      constant := (702632518909291456620911230558547816999999712149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12487144813449494353/25000000000000000000)
  directionHi := (49948579253797977413/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree002.table
  base := (58656478385006202224832030897543364596407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-2648122198534236389427833084040558000000000000)
      constant := (412297654663775794063033124431581758232953995508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree002.table
  base := (14641544180563022316514277050468639973257/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-2650936905089307403993216520023758000000000000)
      constant := (411668123978216206128478180894464415619317827632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12487144813449494353/25000000000000000000)
  centralHi := (49948579253797977413/100000000000000000000)
  directionLo := (70637958201988507279/100000000000000000000)
  directionHi := (882974477524856341/1250000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree003.table
  base := (36812081436441818376684037449701416685711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-437566912524809151638117977237902000000000000)
      constant := (29000044219280797517572617424483418829155842676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree003.table
  base := (36741545809821277739592448997182181307059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-438036030283987654065681883235102000000000000)
      constant := (28945893335327118273826692580228842626184932644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70637958201988507279/100000000000000000000)
  centralHi := (882974477524856341/1250000000000000000)
  directionLo := (43256738516729428587/50000000000000000000)
  directionHi := (3460539081338354287/4000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree004.table
  base := (6213173687343489049839908893284088291539/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-5228082226912328340058290506241678000000000000)
      constant := (179619595579996376889813202691208396657828859664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree004.table
  base := (6200432583844817886149880678977855634677/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-5233711640022470369189057378208078000000000000)
      constant := (179274516008027749760004758517902504701733501552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43256738516729428587/50000000000000000000)
  centralHi := (3460539081338354287/4000000000000000000)
  directionLo := (3995886340303838193/4000000000000000000)
  directionHi := (49948579253797977413/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree005.table
  base := (71647532416685081402631984730654938336229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-6518062241101374315373519217342238000000000000)
      constant := (134066627933560080125768637631774930218725923319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree005.table
  base := (7150193537225992833197330988216245382957/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-6525099007489051851786977807300238000000000000)
      constant := (133830230439607450715407619820198332933335109270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3995886340303838193/4000000000000000000)
  centralHi := (49948579253797977413/50000000000000000000)
  directionLo := (111688418591027998181/100000000000000000000)
  directionHi := (55844209295513999091/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree006.table
  base := (27184362099263402152542644929670306502693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12478532394148164573199899525520000000000000)
      linear := (-78869113689802225158472201297402000000000000)
      constant := (1086339631850083296044600171516638103452272954) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree006.table
  base := (27131176889728690433621324929558917140463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-868498486106181481598322026265822000000000000)
      constant := (11932005108126130915358013090028641076548300154) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111688418591027998181/100000000000000000000)
  centralHi := (55844209295513999091/50000000000000000000)
  directionLo := (122348532548770793521/100000000000000000000)
  directionHi := (61174266274385396761/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree007.table
  base := (5349409535540570490497472975974310721623/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-185673923866927882979672992643742000000000000)
      constant := (1871294048419245761124458980578646127040675176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree007.table
  base := (5339307092892509786319963181434415631799/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-185874974335147241162914666642542000000000000)
      constant := (1869146366305358363529678313079520642118915688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122348532548770793521/100000000000000000000)
  centralHi := (61174266274385396761/50000000000000000000)
  directionLo := (66075759523274804349/50000000000000000000)
  directionHi := (132151519046549608699/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree008.table
  base := (17249892448795621997209448047077193220577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-10388002283668512241319205350643918000000000000)
      constant := (82253086196888688724452068746282061233999737494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree008.table
  base := (34435727559360509383015262899803558557503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-10399261109888796299580739094576718000000000000)
      constant := (82188270467452970370426755275246993585043386133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66075759523274804349/50000000000000000000)
  centralHi := (132151519046549608699/100000000000000000000)
  directionLo := (141275916403977014559/100000000000000000000)
  directionHi := (882974477524856341/625000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree009.table
  base := (1763362586155655656689898453246159409039/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-1297553588650839801848270451304942000000000000)
      constant := (8556148420017167139487041433229264226422393296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree009.table
  base := (14080575851387458043639498920657302712751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12478532394148164573199899525520000000000000)
      linear := (-118087358357125028102814742663322000000000000)
      constant := (777505395723885272922264413693202055371704878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141275916403977014559/100000000000000000000)
  centralHi := (882974477524856341/625000000000000000)
  directionLo := (74922868880696966119/50000000000000000000)
  directionHi := (149845737761393932239/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree010.table
  base := (23247201759650994404621152636779307156139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-12967962312046604191949662772845038000000000000)
      constant := (74741604439316211382494242508925857264209334329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree010.table
  base := (23202760643282687566614990012192298253309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-12982035844821959264776579952761038000000000000)
      constant := (74737685019031553955575354720918766816475507199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74922868880696966119/50000000000000000000)
  centralHi := (149845737761393932239/100000000000000000000)
  directionLo := (31590255266287024507/20000000000000000000)
  directionHi := (19743909541429390317/12500000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree011.table
  base := (19204070102688138433766931230613624708811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-1296176575112331833387717407631418000000000000)
      constant := (6797141802545395103712753639506392667267420011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree011.table
  base := (1916590800644681370537573491934666800377/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-1297583928389867340670409125623018000000000000)
      constant := (6799192174775408659782464234570336892868187770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31590255266287024507/20000000000000000000)
  centralHi := (19743909541429390317/12500000000000000000)
  directionLo := (165660696196177791069/100000000000000000000)
  directionHi := (16566069619617779107/10000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree012.table
  base := (3168510432045986508893107956470233181551/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-1727546926713855126953346688338462000000000000)
      constant := (8518073791978817606994794829911511511165060145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree012.table
  base := (7904729392264630588929442366158178803193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-1729423397750569136663602312327262000000000000)
      constant := (8523449178791392983006988698573528546692981494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165660696196177791069/100000000000000000000)
  centralHi := (16566069619617779107/10000000000000000000)
  directionLo := (173026954066917714349/100000000000000000000)
  directionHi := (3460539081338354287/2000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree013.table
  base := (13004834354884505957232381007802088362829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-16837902354613742117895348906146718000000000000)
      constant := (80147552466068252929220831718182331963958135919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree013.table
  base := (6487999228234259894015360624040900544159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-16856197947221703712570341240037518000000000000)
      constant := (80221805037968030392036326153554822965674453098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173026954066917714349/100000000000000000000)
  centralHi := (3460539081338354287/2000000000000000000)
  directionLo := (180092163636145452033/100000000000000000000)
  directionHi := (90046081818072726017/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree014.table
  base := (10581457354031144681106343827005174900703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-369956783036791593738991379943822000000000000)
      constant := (1735337519498734211649353601756255945776224517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree014.table
  base := (5278144453756925565465772684636569864969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-370358883973230310105474727941422000000000000)
      constant := (1737389841242759602849785929866300740808254182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180092163636145452033/100000000000000000000)
  centralHi := (90046081818072726017/50000000000000000000)
  directionLo := (93445235261918421687/50000000000000000000)
  directionHi := (1495123764190694747/800000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree015.table
  base := (1698516409501766851308605848803033179177/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-2157540264776870452058422925371982000000000000)
      constant := (10130534107552705388336936806970881964855407415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree015.table
  base := (4235308509634322221563725510063086155217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-2159885853572762964196242455357982000000000000)
      constant := (10144704407569295573136510824888710481991937286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93445235261918421687/50000000000000000000)
  centralHi := (1495123764190694747/800000000000000000)
  directionLo := (12090625976042553281/6250000000000000000)
  directionHi := (193450015616680852497/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree016.table
  base := (6677737707204417196357537331168863631673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-20707842397180880043841035039448398000000000000)
      constant := (98471460999427598665572590261003524849285706003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree016.table
  base := (416161786212472883734800145007849836837/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-20730360049621448160364102527313998000000000000)
      constant := (98626754370678879807324456503250715529874553712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12090625976042553281/6250000000000000000)
  centralHi := (193450015616680852497/100000000000000000000)
  directionLo := (199794317015191909651/100000000000000000000)
  directionHi := (49948579253797977413/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree017.table
  base := (2544951131960354579983289016239038335303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-1999802037397266001741478522777178000000000000)
      constant := (9712650453179714226925599956237833284037145806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree017.table
  base := (317077055985475310141340343677145714793/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-22021747417088029642962022956406158000000000000)
      constant := (107023090735809429441816204778724804389573829168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199794317015191909651/100000000000000000000)
  centralHi := (49948579253797977413/25000000000000000000)
  directionLo := (205943268112944010209/100000000000000000000)
  directionHi := (20594326811294401021/10000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree018.table
  base := (1845931706536082808932059878231898426471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-2587533602839885777163499162405502000000000000)
      constant := (12912524703055173996199852438470035127848601418) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree018.table
  base := (3677376343955304332659007026122054064779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-2590348309394956791728882598388702000000000000)
      constant := (12936249989280621167813194657594179157870633041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205943268112944010209/100000000000000000000)
  centralHi := (20594326811294401021/10000000000000000000)
  directionLo := (211913874605965521839/100000000000000000000)
  directionHi := (2648923432574569023/1250000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree019.table
  base := (613458121654111385878085446291833653459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (708246)
      previous := (354123)
      next := (354123)
      square := (3422090601165286129492493221680000000000000)
      linear := (-68082499833097002686389809342798000000000000)
      constant := (350526306880431110811632919630273740211718436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree019.table
  base := (1220631161239661846561430150124803746579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (708246)
      previous := (354123)
      next := (354123)
      square := (3422090601165286129492493221680000000000000)
      linear := (-68156571058230450438110426079198000000000000)
      constant := (351202553423787037981218762671082845949309458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211913874605965521839/100000000000000000000)
  centralHi := (2648923432574569023/1250000000000000000)
  directionLo := (43544161868147521651/20000000000000000000)
  directionHi := (3401887645949025129/1562500000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree020.table
  base := (675892381053817686202035000978262823789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-25867762453937063945101949883850638000000000000)
      constant := (137778905995774820868569862747550149235820716958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree020.table
  base := (335223593965941248840389877469803393037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-2354173592680706735523253113062058000000000000)
      constant := (12550425775127601558861214353249640679899533748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43544161868147521651/20000000000000000000)
  centralHi := (3401887645949025129/1562500000000000000)
  directionLo := (223376837182055996363/100000000000000000000)
  directionHi := (55844209295513999091/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree021.table
  base := (73249635898817660983481670513256485151/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (579766)
      previous := (289883)
      next := (289883)
      square := (2801303190523057353167324383280000000000000)
      linear := (-61582182467406144944256640804878000000000000)
      constant := (339898753463852678274143192785053707512673105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree021.table
  base := (356826119989698405733559305547526314121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (579766)
      previous := (289883)
      next := (289883)
      square := (2801303190523057353167324383280000000000000)
      linear := (-61649199290145931005337198804478000000000000)
      constant := (340598368260761416295187440657197226993374491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223376837182055996363/100000000000000000000)
  centralHi := (55844209295513999091/25000000000000000000)
  directionLo := (228893145286030118801/100000000000000000000)
  directionHi := (114446572643015059401/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree022.table
  base := (-518612890122904402159704680907213643597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-2586156589301377808702946118731978000000000000)
      constant := (14805599827424447737915654757788596680725714003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree022.table
  base := (-131688630162310710934150883658271634267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-2588971295856448823268329554715178000000000000)
      constant := (14836729285018549361201800430202693990212237332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228893145286030118801/100000000000000000000)
  centralHi := (114446572643015059401/50000000000000000000)
  directionLo := (117139801656401815113/50000000000000000000)
  directionHi := (234279603312803630227/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree023.table
  base := (-263141635712693443840070349605821156023/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-29737702496504201871047636017152318000000000000)
      constant := (176655041803734050869208509260120160637699030735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree023.table
  base := (-1322735686137903720816913775547165948013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-29770071621887518538549545530959118000000000000)
      constant := (177032538870342270867749847724864795973014206257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117139801656401815113/50000000000000000000)
  centralHi := (234279603312803630227/100000000000000000000)
  directionLo := (119772485465024027179/50000000000000000000)
  directionHi := (239544970930048054359/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree024.table
  base := (-203558177813084410522905518866086316149/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-3447520278965916427373651636472542000000000000)
      constant := (21250801828147550246508752888914925906900437290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree024.table
  base := (-2041641780740396191795925947881298568179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-3451273221039344446794162884450142000000000000)
      constant := (21296777795099412054352404937721252805902298359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119772485465024027179/50000000000000000000)
  centralHi := (239544970930048054359/100000000000000000000)
  directionLo := (122348532548770793521/50000000000000000000)
  directionHi := (244697065097541587043/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree025.table
  base := (-671714684307891194682619866170777292631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-32317662524882293821678093439353438000000000000)
      constant := (206653017770805581850345754819062652706377495436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree025.table
  base := (-1346040012318462134684731876621973222329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-32352846356820681503745386389143438000000000000)
      constant := (207104332933202360588208128755791615302704019162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122348532548770793521/50000000000000000000)
  centralHi := (244697065097541587043/100000000000000000000)
  directionLo := (31217862033623735883/12500000000000000000)
  directionHi := (49948579253797977413/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree026.table
  base := (-3276603591890383063414721958163744629877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-33607642539071339796993322150453998000000000000)
      constant := (222830074262970494596136262370056608602968468953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree026.table
  base := (-3281098923234467860514473146610794622971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-33644233724287262986343306818235598000000000000)
      constant := (223320193782062964474982296171006891737512332119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31217862033623735883/12500000000000000000)
  centralHi := (49948579253797977413/20000000000000000000)
  directionLo := (254688780291351626251/100000000000000000000)
  directionHi := (63672195072837906563/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree027.table
  base := (-1905304780677163308214457530617867615599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-3877513617028931752478727873506062000000000000)
      constant := (26642026753394653767272223532184070874448724358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree027.table
  base := (-476809671954424307385050216758350009339/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-3881735676861538274326803027480862000000000000)
      constant := (26700940292311173785358062410381940108262613752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254688780291351626251/100000000000000000000)
  centralHi := (63672195072837906563/25000000000000000000)
  directionLo := (259540431100376571523/100000000000000000000)
  directionHi := (64885107775094142881/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree028.table
  base := (-4293632576650856195747200931640609831949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (474354)
      previous := (237177)
      next := (237177)
      square := (2291975337700683288955083586320000000000000)
      linear := (-67138409216047183205238923140362000000000000)
      constant := (477716491066454952127744615242415658655997699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree028.table
  base := (-537119824376194680630847180431319143573/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-739326703249396447990594850539182000000000000)
      constant := (5266547614537485046133093800837656681022756424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259540431100376571523/100000000000000000000)
  centralHi := (64885107775094142881/25000000000000000000)
  directionLo := (66075759523274804349/25000000000000000000)
  directionHi := (264303038093099217397/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree029.table
  base := (-945916222612188930252589173117278577263/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-37477582581638477722939008283755678000000000000)
      constant := (275956073410867232724914657963124064327163422535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree029.table
  base := (-591554977365092251220528349259406626841/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-37518395826687007434137068105512078000000000000)
      constant := (276570480341380267227993077796317054092825164392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66075759523274804349/25000000000000000000)
  centralHi := (264303038093099217397/100000000000000000000)
  directionLo := (67245332790980368579/25000000000000000000)
  directionHi := (268981331163921474317/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree030.table
  base := (-5121670453502113467115685629336769416833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-4307506955091947077583804110539582000000000000)
      constant := (32797029368875849863763273584807590743642051693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree030.table
  base := (-32025790273077079902418342225572866827/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-4312198132683732101859443170511582000000000000)
      constant := (32870198999181130248088539438165601143307066720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67245332790980368579/25000000000000000000)
  centralHi := (268981331163921474317/100000000000000000000)
  directionLo := (273579635726397098043/100000000000000000000)
  directionHi := (68394908931599274511/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree031.table
  base := (-2736274117729356730447568543789007642339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-40057542610016569673569465705956798000000000000)
      constant := (315136124839978859864096654855770679275303754942) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree031.table
  base := (-171083045041448055841129088444841728929/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-3645560960147288218121173542154218000000000000)
      constant := (28712740333571626802386634233395756061208776672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273579635726397098043/100000000000000000000)
  centralHi := (68394908931599274511/25000000000000000000)
  directionLo := (139050959771643673773/50000000000000000000)
  directionHi := (278101919543287347547/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree032.table
  base := (-5784396760719015083165348598371733904371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-41347522624205615648884694417057358000000000000)
      constant := (335840833300258927111593518051461733497592556719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree032.table
  base := (-2893103771307533564226015752879829008113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-41392557929086751881930829392788558000000000000)
      constant := (336591729958867895821547521449541779525746850314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139050959771643673773/50000000000000000000)
  centralHi := (278101919543287347547/100000000000000000000)
  directionLo := (282551832807954029119/100000000000000000000)
  directionHi := (882974477524856341/312500000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree033.table
  base := (-6059016468339108904303472675006485811351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12478532394148164573199899525520000000000000)
      linear := (-430681844832269309335352758870282000000000000)
      constant := (3608931684364070657500195032529221272483012161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree033.table
  base := (-6060570589859195699430317219981490265053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12478532394148164573199899525520000000000000)
      linear := (-431150962591447811762916664867482000000000000)
      constant := (3617004125909100687304300315310543418701477483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282551832807954029119/100000000000000000000)
  centralHi := (882974477524856341/312500000000000000)
  directionLo := (143466371314506090917/50000000000000000000)
  directionHi := (57386548525802436367/20000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree034.table
  base := (-6297894115566265077162242241877557668257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-43927482652583707599515151839258478000000000000)
      constant := (379463731569685314595226638085301002358213990773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree034.table
  base := (-3149613802889535811645402841772374907177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-43975332664019914847126670250972878000000000000)
      constant := (380312585604407987933390439253084227132855317306) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143466371314506090917/50000000000000000000)
  centralHi := (57386548525802436367/20000000000000000000)
  directionLo := (72811940711190995163/25000000000000000000)
  directionHi := (291247762844763980653/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree035.table
  base := (-6502258528467128389040387721053445736237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-922805360546382726016946541844062000000000000)
      constant := (8211778894274712051736843074388265902832625857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree035.table
  base := (-6503402441345710647255475798523455526529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-923810612887479516933154911838062000000000000)
      constant := (8230145268485839837441495850336390222937380069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72811940711190995163/25000000000000000000)
  centralHi := (291247762844763980653/100000000000000000000)
  directionLo := (4617184061217861249/1562500000000000000)
  directionHi := (295499779917943119937/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree036.table
  base := (-1334625247313982763930047281122594937101/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-5167493631217977727793956584606622000000000000)
      constant := (47335862149297565336590924612036124998669122605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree036.table
  base := (-1334821463437137658218677795843860843229/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-5173123044328119756924723456573022000000000000)
      constant := (47441692611922197156033778405282199004926722045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4617184061217861249/1562500000000000000)
  centralHi := (295499779917943119937/100000000000000000000)
  directionLo := (299691475522787864477/100000000000000000000)
  directionHi := (149845737761393932239/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree037.table
  base := (-53213584888817868010894770148078594083/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-47797422695150845525460837972560158000000000000)
      constant := (450399038277813334325554087958349742558696382336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree037.table
  base := (-3406090066355425505853959385080755295021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-47849494766419659294920431538249358000000000000)
      constant := (451405464320221935996762352507965686878101959138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299691475522787864477/100000000000000000000)
  centralHi := (149845737761393932239/50000000000000000000)
  directionLo := (37978168290829168371/12500000000000000000)
  directionHi := (303825346326633346969/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree038.table
  base := (-6917593809244458078534894001751313887511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (708246)
      previous := (354123)
      next := (354123)
      square := (3422090601165286129492493221680000000000000)
      linear := (-135976184790415211913507109927038000000000000)
      constant := (1317187759942539390621739334037518376331684139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree038.table
  base := (-6918315062338381424509260484041250439247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (708246)
      previous := (354123)
      next := (354123)
      square := (3422090601165286129492493221680000000000000)
      linear := (-136124327240682107416948343399838000000000000)
      constant := (1320129071880048055476158542116419894119212803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37978168290829168371/12500000000000000000)
  centralHi := (303825346326633346969/100000000000000000000)
  directionLo := (38487965172564745083/12500000000000000000)
  directionHi := (61580744276103592133/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree039.table
  base := (-6992469410126399388359673041358456424929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12478532394148164573199899525520000000000000)
      linear := (-508862451752817550263548438330922000000000000)
      constant := (5064030057850087510420877394601903264299430919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree039.table
  base := (-1748271917988881905204452483162588947341/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-5603585500150313584457363599603742000000000000)
      constant := (55828624161712559653049707507306854420861342244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38487965172564745083/12500000000000000000)
  centralHi := (61580744276103592133/20000000000000000000)
  directionLo := (311928777462812127199/100000000000000000000)
  directionHi := (389910971828515159/125000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree040.table
  base := (-7036445658511790757338434021461077570219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-51667362737717983451406524105861838000000000000)
      constant := (527900780877580917557145323681214844887179214791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree040.table
  base := (-140739511151603297606346523075246371723/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-51723656868819403742714192825525838000000000000)
      constant := (529077695468968943162014478744869656306429672350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311928777462812127199/100000000000000000000)
  centralHi := (389910971828515159/125000000000000000)
  directionLo := (31590255266287024507/10000000000000000000)
  directionHi := (315902552662870245071/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree041.table
  base := (-704992121851427195794739268862828527329/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-52957342751907029426721752816962398000000000000)
      constant := (555189498645542370871285438180658364918276545810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree041.table
  base := (-1410075064235653591825764759517895877073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-53015044236285985225312113254617998000000000000)
      constant := (556426134455639630261953129054738478216075572985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31590255266287024507/10000000000000000000)
  centralHi := (315902552662870245071/100000000000000000000)
  directionLo := (79956739611332345099/25000000000000000000)
  directionHi := (319826958445329380397/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree042.table
  base := (-3516613724806479779903123513915130886927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (579766)
      previous := (289883)
      next := (289883)
      square := (2801303190523057353167324383280000000000000)
      linear := (-123009802190694048530696103238238000000000000)
      constant := (1322459294219225034619244727065672030496025766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree042.table
  base := (-7033616547200438554095286773781502303261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (254663926411187032106120398480000000000000)
      linear := (-11194894166924874604805201748858000000000000)
      constant := (120491106420018506602583636322400877668522779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79956739611332345099/25000000000000000000)
  centralHi := (319826958445329380397/100000000000000000000)
  directionLo := (323703790397739062361/100000000000000000000)
  directionHi := (161851895198869531181/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree043.table
  base := (-6986639963839560941331825508250918011783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-55537302780285121377352210239163518000000000000)
      constant := (611945448538166867434685070446775820617667480787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree043.table
  base := (-1746743330172000815235236949856993891179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-55597818971219148190507954112802318000000000000)
      constant := (613305883851840072374529921679827019483338128924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323703790397739062361/100000000000000000000)
  centralHi := (161851895198869531181/50000000000000000000)
  directionLo := (327534737833006533919/100000000000000000000)
  directionHi := (2047092111456290837/625000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree044.table
  base := (-6910388160738141050032203289127816411661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-5166116617679469759333403540933098000000000000)
      constant := (58310163298273026441208119255038014499447157139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree044.table
  base := (-1727668432059105959722281209276741824433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-5171746030789611788464170412899498000000000000)
      constant := (58439664986625054146846546256523205699233767868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327534737833006533919/100000000000000000000)
  centralHi := (2047092111456290837/625000000000000000)
  directionLo := (331321392392355582139/100000000000000000000)
  directionHi := (16566069619617779107/5000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree045.table
  base := (-6804663101120121959175962799366508305309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-6457473645407023703109185295707182000000000000)
      constant := (74622584154599208806949877911998029180461280089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree045.table
  base := (-6804907702240327991855360238672003151037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-6464510411794701239522643885665182000000000000)
      constant := (74788146403879735208386426709802180298874371577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331321392392355582139/100000000000000000000)
  centralHi := (16566069619617779107/5000000000000000000)
  directionLo := (67013051154616798909/20000000000000000000)
  directionHi := (167532627886541997273/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree046.table
  base := (-5335699211873041210224743810957769101/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-59407242822852259303297896372465198000000000000)
      constant := (702519553024260631064243538049237600768585861250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree046.table
  base := (-6669833503101386332116537386872206618689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-59471981073618892638301715400078798000000000000)
      constant := (704076615050609866160431403153632624175079017621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67013051154616798909/20000000000000000000)
  centralHi := (167532627886541997273/50000000000000000000)
  directionLo := (84691936671885688601/25000000000000000000)
  directionHi := (67753549337508550881/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree047.table
  base := (-6505403684269626950766198674736057244099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-60697222837041305278613125083565758000000000000)
      constant := (734160450649663191004407264943675385457504146111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree047.table
  base := (-6505583080575680395830340251054114230757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-60763368441085474120899635829170958000000000000)
      constant := (735785976028088046167156463216350949563841803273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84691936671885688601/25000000000000000000)
  centralHi := (67753549337508550881/20000000000000000000)
  directionLo := (17121510357239812779/5000000000000000000)
  directionHi := (342430207144796255581/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree048.table
  base := (-3156056450735759878980418324376757654381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-6887466983470039028214261532740702000000000000)
      constant := (85169528471923903227574565159727165744736398802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree048.table
  base := (-6312266511848319419833614245868674390687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-6894972867616895067055284028695902000000000000)
      constant := (85357911977663860507100303520104255205734514227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17121510357239812779/5000000000000000000)
  centralHi := (342430207144796255581/100000000000000000000)
  directionLo := (173026954066917714349/50000000000000000000)
  directionHi := (346053908133835428699/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree049.table
  base := (-95153815024188633423286321853873000863/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-1291371078886110147535583316444222000000000000)
      constant := (16318679751811795218655532415834436700618063552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree049.table
  base := (-1217995135675173015331393017535172001013/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-1292778432163645654818275034435822000000000000)
      constant := (16354737744070459888317473754698820439278981965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173026954066917714349/50000000000000000000)
  centralHi := (346053908133835428699/100000000000000000000)
  directionLo := (34964005477658584189/10000000000000000000)
  directionHi := (349640054776585841891/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree050.table
  base := (-1167734945097572726811011410221463044393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-5869742079964403927687164656078858000000000000)
      constant := (75766270011250784703551087359929814309347950035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree050.table
  base := (-2919393657259135218864822940421747175989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-64637530543485218568693397116447438000000000000)
      constant := (835268666631466188279946216356109583412378254642) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34964005477658584189/10000000000000000000)
  centralHi := (349640054776585841891/100000000000000000000)
  directionLo := (353189791009942536399/100000000000000000000)
  directionHi := (882974477524856341/250000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree051.table
  base := (-2779334581073796590272398978532125431257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-7317460321533054353319337769774222000000000000)
      constant := (96440736669840557379796652774365542131422888394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree051.table
  base := (-5558765537268288959565458144206650762911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-7325435323439088894587924171726622000000000000)
      constant := (96653405225848078783081971992993306101203540531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353189791009942536399/100000000000000000000)
  centralHi := (882974477524856341/250000000000000000)
  directionLo := (356704203848398489013/100000000000000000000)
  directionHi := (178352101924199244507/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree052.table
  base := (-328117591220977866793043371070709225673/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-67147122907986535155189268639068558000000000000)
      constant := (903228193008802968389859077423443431619199359952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree052.table
  base := (-328122746686748148114657653604636181353/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-67220305278418381533889237974631758000000000000)
      constant := (905217996797408471365287889191869959491466104272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356704203848398489013/100000000000000000000)
  centralHi := (178352101924199244507/50000000000000000000)
  directionLo := (360184327272290904067/100000000000000000000)
  directionHi := (90046081818072726017/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree053.table
  base := (-2456178389827726917411983500536137254543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-68437102922175581130504497350169118000000000000)
      constant := (939213579976275295259222325428748370084668996854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree053.table
  base := (-4912427373177435773854379502263188745003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-6228335695080451183317014400338538000000000000)
      constant := (85570967038170885331966582217032322088606777397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360184327272290904067/100000000000000000000)
  centralHi := (90046081818072726017/25000000000000000000)
  directionLo := (90907786445271596317/25000000000000000000)
  directionHi := (363631145781086385269/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree054.table
  base := (-4546132918115256150938424837906324307001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-7747453659596069678424414006807742000000000000)
      constant := (108435858304766344119196086477145503322668052421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree054.table
  base := (-4546193326280895934170158535955293748927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-7755897779261282722120564314757342000000000000)
      constant := (108674278134593777125898208352266362897627533267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90907786445271596317/25000000000000000000)
  centralHi := (363631145781086385269/100000000000000000000)
  directionLo := (367045597646312380563/100000000000000000000)
  directionHi := (91761399411578095141/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree055.table
  base := (-1037810379750267781363740051517239525637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-6456096631868515734648632252033658000000000000)
      constant := (92123233808472441238415897597248580801116255852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree055.table
  base := (-41512932058516466567422064964374391971/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-6463133398256193271062090841991658000000000000)
      constant := (92325594471323464646180970583627403242382482900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367045597646312380563/100000000000000000000)
  centralHi := (91761399411578095141/25000000000000000000)
  directionLo := (92607144473648594367/25000000000000000000)
  directionHi := (370428577894594377469/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree056.table
  base := (-931927271677978652912634412865826617851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-1475653938055973858294901703744302000000000000)
      constant := (21459430102293458366473869487665864890018492444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree056.table
  base := (-3727753306623337706108083039114391919141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-1477262341801728723760835095734702000000000000)
      constant := (21506524475344801633439739260289122747201819801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92607144473648594367/25000000000000000000)
  centralHi := (370428577894594377469/100000000000000000000)
  directionLo := (373780941047673686749/100000000000000000000)
  directionHi := (1495123764190694747/400000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree057.table
  base := (-3275557829222057299940182953322795658409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (78694)
      previous := (39347)
      next := (39347)
      square := (380232289018365125499165913520000000000000)
      linear := (-22652207749748157904513823390142000000000000)
      constant := (335608555004492485542218093124688013140117549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree057.table
  base := (-327559565682101685858851060543670192777/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (78694)
      previous := (39347)
      next := (39347)
      square := (380232289018365125499165913520000000000000)
      linear := (-22676898158125973821754028968942000000000000)
      constant := (336344396724310706920078525240313617660931970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373780941047673686749/100000000000000000000)
  centralHi := (1495123764190694747/400000000000000000)
  directionLo := (75420700728634827423/20000000000000000000)
  directionHi := (94275875910793534279/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree058.table
  base := (-2794806361280769378887806035226627224177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-74887002993120811007080640905671918000000000000)
      constant := (1129995899886493046134730619308005256912121771653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree058.table
  base := (-139741935855447601167315919046551130253/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-74968629483217870429476760549184718000000000000)
      constant := (1132471243852210398072881443413921906972770272340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75420700728634827423/20000000000000000000)
  centralHi := (94275875910793534279/25000000000000000000)
  directionLo := (380397046557186596959/100000000000000000000)
  directionHi := (2377481540982416231/625000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree059.table
  base := (-2285470291154424999797408586956321166721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-76176983007309856982395869616772478000000000000)
      constant := (1170323161709702576437532477030145100853305350869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree059.table
  base := (-91419918547287678349192686297368525651/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-76260016850684451912074680978276878000000000000)
      constant := (1172884568874587006376030264788512486170654665975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380397046557186596959/100000000000000000000)
  centralHi := (2377481540982416231/625000000000000000)
  directionLo := (38366231714738851211/10000000000000000000)
  directionHi := (383662317147388512111/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree060.table
  base := (-873781355235254265985598989779007914271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-8607440335722100328634566480874782000000000000)
      constant := (134597106417002513100580229984008200838098126182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree060.table
  base := (-873793187488492446990418450542222764223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-8616822690905670377185844600818782000000000000)
      constant := (134891433032937221221666975370302209673520505766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38366231714738851211/10000000000000000000)
  centralHi := (383662317147388512111/100000000000000000000)
  directionLo := (386900031233361704993/100000000000000000000)
  directionHi := (193450015616680852497/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree061.table
  base := (-295273650846012552518732054639974200517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-7159722094153449903002393367179418000000000000)
      constant := (113922569889170914171410922549819668869213972332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree061.table
  base := (-1181114838147850946940682057815635950101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-78842791585617614877270521836461198000000000000)
      constant := (1255886210052049597599713995446475730352187677689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386900031233361704993/100000000000000000000)
  centralHi := (193450015616680852497/50000000000000000000)
  directionLo := (195055437464486747233/50000000000000000000)
  directionHi := (390110874928973494467/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree062.table
  base := (-117215037705701689366625791691604672497/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-80046923049876994908341555750074158000000000000)
      constant := (1295646078649502573038020975305193052449359280665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree062.table
  base := (-146523122177677397757228740950431435201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-80134178953084196359868442265553358000000000000)
      constant := (1298474491143214857333197370951486512063720886356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195055437464486747233/50000000000000000000)
  centralHi := (390110874928973494467/100000000000000000000)
  directionLo := (393295506340108262207/100000000000000000000)
  directionHi := (6145242286564191597/1562500000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree063.table
  base := (37487795067825713601878240376887655933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (579766)
      previous := (289883)
      next := (289883)
      square := (2801303190523057353167324383280000000000000)
      linear := (-184437421913981952117135565671598000000000000)
      constant := (3035980439469883666156470567881055620881709943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree063.table
  base := (18736502760368939377226645879309540319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (579766)
      previous := (289883)
      next := (289883)
      square := (2801303190523057353167324383280000000000000)
      linear := (-184638472382201310300377239670398000000000000)
      constant := (3042602555877485420718672654032257476369213498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393295506340108262207/100000000000000000000)
  centralHi := (6145242286564191597/1562500000000000000)
  directionLo := (198227278569824413047/50000000000000000000)
  directionHi := (79290911427929765219/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree064.table
  base := (689587848806504123643212066217684983419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-82626883078255086858972013172275278000000000000)
      constant := (1382812142870611340117484013430282770337498170409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree064.table
  base := (344787603479152563200070939001681735023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-7519723062547032665914934829430698000000000000)
      constant := (125984173343158453802659695925781645467794793246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198227278569824413047/50000000000000000000)
  centralHi := (79290911427929765219/20000000000000000000)
  directionLo := (399588634030383819303/100000000000000000000)
  directionHi := (49948579253797977413/12500000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree065.table
  base := (1370219514354807753039545039614598313153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-83916863092444132834287241883375838000000000000)
      constant := (1427480376283988203839776996842790065326574978283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree065.table
  base := (342552177383063948656621190450698481177/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-84008341055483940807662203552829838000000000000)
      constant := (1430589020574361832134191831562061052551681821388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399588634030383819303/100000000000000000000)
  centralHi := (49948579253797977413/12500000000000000000)
  directionLo := (100674580026359233199/25000000000000000000)
  directionHi := (402698320105436932797/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree066.table
  base := (2079378206059073477897838697122419579397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12478532394148164573199899525520000000000000)
      linear := (-860675182895284634440428995903802000000000000)
      constant := (14877495616322243948374006251438980479939953533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree066.table
  base := (207936897235433202450405537739349158833/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12478532394148164573199899525520000000000000)
      linear := (-861613418413641639295556807898202000000000000)
      constant := (14909869298876506308266126358969265472705969370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100674580026359233199/25000000000000000000)
  centralHi := (402698320105436932797/100000000000000000000)
  directionLo := (202892088057428873913/50000000000000000000)
  directionHi := (405784176114857747827/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree067.table
  base := (352132508822119305976864639077029988163/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-86496823120822224784917699305576958000000000000)
      constant := (1518987205318337676694991483462524649100807323144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree067.table
  base := (281705218042177147575560113823920125643/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-86591115790417103772858044411014158000000000000)
      constant := (1522290020137105066541041421331966045871474036730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202892088057428873913/50000000000000000000)
  centralHi := (405784176114857747827/100000000000000000000)
  directionLo := (10221168541154150579/2500000000000000000)
  directionHi := (408846741646166023161/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree068.table
  base := (3583261869262846839010299022304601986553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-87786803135011270760232928016677518000000000000)
      constant := (1565825788519742974739825150178541308349473465683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree068.table
  base := (3583255127921797727072765120387424520429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-87882503157883685255455964840106318000000000000)
      constant := (1569227893605300060192740737906935566081844989519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10221168541154150579/2500000000000000000)
  centralHi := (408846741646166023161/100000000000000000000)
  directionLo := (411886536225888020419/100000000000000000000)
  directionHi := (20594326811294401021/5000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree069.table
  base := (4377980879582466503300806552036967511003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-9897420349911146303949795191975342000000000000)
      constant := (179265312316931784305122623103593334101323452737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree069.table
  base := (2188987560217125449460878651974666934563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-9908210058372251859783765029910942000000000000)
      constant := (179654519586095653652294023478705145434920667954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411886536225888020419/100000000000000000000)
  centralHi := (20594326811294401021/5000000000000000000)
  directionLo := (2593150377177831049/625000000000000000)
  directionHi := (414904060348452967841/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree070.table
  base := (650151851556162563108541507009294301187/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-1844219656395701279813538478344462000000000000)
      constant := (33911699353216192802224079441133031352240977544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree070.table
  base := (5201209892943699121862833336151058363017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-1846230161077894861645955218332462000000000000)
      constant := (33985272738352399900311110150784342674835864563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2593150377177831049/625000000000000000)
  centralHi := (414904060348452967841/100000000000000000000)
  directionLo := (417899796438219912167/100000000000000000000)
  directionHi := (52237474554777489021/12500000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree071.table
  base := (6052961742888814759927330605365656398049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-91656743177578408686178614149979198000000000000)
      constant := (1710682157514328561621053836307328379506483787339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree071.table
  base := (6052957541082891582331498779315921446959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-91756665260283429703249726127382798000000000000)
      constant := (1714390953983571319262062204278496802113050517349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417899796438219912167/100000000000000000000)
  centralHi := (52237474554777489021/12500000000000000000)
  directionLo := (84174841949974239961/20000000000000000000)
  directionHi := (210437104874935599903/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree072.table
  base := (6933220051863553236415887491068017608701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12478532394148164573199899525520000000000000)
      linear := (-938855789815832875368624675364442000000000000)
      constant := (17781964400376921204716790518066486163480311989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree072.table
  base := (1733304115863600878147140516300912785429/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-10338672514194445687316405172941662000000000000)
      constant := (196025382542598585520684701619236525235503957564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84174841949974239961/20000000000000000000)
  centralHi := (210437104874935599903/50000000000000000000)
  directionLo := (211913874605965521839/50000000000000000000)
  directionHi := (423827749211931043679/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree073.table
  base := (3920994188724112671323255580010461691131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-94236703205956500636809071572180318000000000000)
      constant := (1810870220291534810184345523788978010257174419282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree073.table
  base := (784198531323133966252786824786572604269/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-94339439995216592668445566985567118000000000000)
      constant := (1814790828520137372329711078563279109968945197590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211913874605965521839/50000000000000000000)
  centralHi := (423827749211931043679/100000000000000000000)
  directionLo := (426760848217739455193/100000000000000000000)
  directionHi := (213380424108869727597/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree074.table
  base := (4389632786920312968592710155254793292521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-95526683220145546612124300283280878000000000000)
      constant := (1862049389470445968905268230221358765633177985862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree074.table
  base := (8779262957533040419047987325696679156341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-95630827362683174151043487414659278000000000000)
      constant := (1866078108909908554390989527914406439202055078951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426760848217739455193/100000000000000000000)
  centralHi := (213380424108869727597/50000000000000000000)
  directionLo := (214836962683913746749/50000000000000000000)
  directionHi := (429673925367827493499/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree075.table
  base := (4872525338470881901479501074057448556059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-10757407026037176954159947666042382000000000000)
      constant := (212661331276189768546831964672266323565178808322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree075.table
  base := (9745048443317832200090704481089101008619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12478532394148164573199899525520000000000000)
      linear := (-979012270001512683168095028724762000000000000)
      constant := (19374649317007310642774625395934885107741461491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214836962683913746749/50000000000000000000)
  centralHi := (429673925367827493499/100000000000000000000)
  directionLo := (27035461572955892867/6250000000000000000)
  directionHi := (432567385167294285873/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree076.table
  base := (1342417859430646216980156680148653924959/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (708246)
      previous := (354123)
      next := (354123)
      square := (3422090601165286129492493221680000000000000)
      linear := (-271763554705051630367741711095518000000000000)
      constant := (5447584473453052191112402152439876961519808872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree076.table
  base := (10739340968740228090418846299888785977683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (708246)
      previous := (354123)
      next := (354123)
      square := (3422090601165286129492493221680000000000000)
      linear := (-272059839605585421374624178041118000000000000)
      constant := (5459355533344549399098301472911208500777740233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27035461572955892867/6250000000000000000)
  centralHi := (432567385167294285873/100000000000000000000)
  directionLo := (43544161868147521651/10000000000000000000)
  directionHi := (435441618681475216511/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree077.table
  base := (11762141486547878594190813597235488311029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (474354)
      previous := (237177)
      next := (237177)
      square := (2291975337700683288955083586320000000000000)
      linear := (-184409319596869544597532442331322000000000000)
      constant := (3747546249660938177600886468345097101522533221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree077.table
  base := (183783435298303926333493238848536560731/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (474354)
      previous := (237177)
      next := (237177)
      square := (2291975337700683288955083586320000000000000)
      linear := (-184610370065088902780774116330122000000000000)
      constant := (3755638781427322562102913400139253298292161216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43544161868147521651/10000000000000000000)
  centralHi := (435441618681475216511/100000000000000000000)
  directionLo := (219148502076455113051/50000000000000000000)
  directionHi := (438297004152910226103/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree078.table
  base := (12813445935539725197123481194535081190377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-11187400364100192279265023903075902000000000000)
      constant := (230444475714594518227867574112900327562942366283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree078.table
  base := (12813444546585392611770389716455449907081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-11199597425838833342381685459003102000000000000)
      constant := (230941794260582673033390492625618080987469913899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219148502076455113051/50000000000000000000)
  centralHi := (438297004152910226103/100000000000000000000)
  directionLo := (441133907582367943393/100000000000000000000)
  directionHi := (220566953791183971697/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree079.table
  base := (1389325573864808967040979546430718272577/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-101976583291090776488700443838783678000000000000)
      constant := (2128796552661678866540799010542724972768378407470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree079.table
  base := (13893254553371830867480835169172031254069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-102087764200016081564033089560120078000000000000)
      constant := (2133387882168317358333860940773056694024469427559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441133907582367943393/100000000000000000000)
  centralHi := (220566953791183971697/50000000000000000000)
  directionLo := (221976341638226211789/50000000000000000000)
  directionHi := (443952683276452423579/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree080.table
  base := (15001570488616001918474134271405657126847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-103266563305279822464015672549884238000000000000)
      constant := (2184316241545037399338807256202962012222762861717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree080.table
  base := (15001569477258850971820051298217689377659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-103379151567482663046631009989212238000000000000)
      constant := (2189024503954223858273201179470430938032739595049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221976341638226211789/50000000000000000000)
  centralHi := (443952683276452423579/100000000000000000000)
  directionLo := (446753674364111992727/100000000000000000000)
  directionHi := (55844209295513999091/12500000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree081.table
  base := (16138389842575833510859003753668321274481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-11617393702163207604370100140109422000000000000)
      constant := (248951038608999188888167000634773685285267238499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree081.table
  base := (16138388979710140490105349240628080436609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-11630059881661027169914325602033822000000000000)
      constant := (249487334790012782542609115941809423263274942611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446753674364111992727/100000000000000000000)
  centralHi := (55844209295513999091/12500000000000000000)
  directionLo := (112384303321045449179/25000000000000000000)
  directionHi := (449537213284181796717/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree082.table
  base := (4325928377962846499332887258828926404547/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-105846523333657914414646129972085358000000000000)
      constant := (2297525869964011834340655531052859798151332625668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree082.table
  base := (4325928193938233535895227902615646068161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-105961926302415826011826850847396558000000000000)
      constant := (2302472409136943470908128279070367848666681171884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112384303321045449179/25000000000000000000)
  centralHi := (449537213284181796717/100000000000000000000)
  directionLo := (226151811122960549991/50000000000000000000)
  directionHi := (452303622245921099983/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree083.table
  base := (18497541253380290166840371411557428052827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-9739682122531541853632850789380538000000000000)
      constant := (214110528051676482521073663749585203103438111227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree083.table
  base := (2312192578186382447347620296812347579229/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-107253313669882407494424771276488718000000000000)
      constant := (2360283691614600326463854731139764588132553570552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226151811122960549991/50000000000000000000)
  centralHi := (452303622245921099983/100000000000000000000)
  directionLo := (227526606832175690423/50000000000000000000)
  directionHi := (455053213664351380847/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree084.table
  base := (3081230134765335334790155934489575821/1562500000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (579766)
      previous := (289883)
      next := (289883)
      square := (2801303190523057353167324383280000000000000)
      linear := (-245865041637269855703575028104958000000000000)
      constant := (5473082002122155491597373629324503875745222400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree084.table
  base := (394397446539333822949798532912982266117/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (579766)
      previous := (289883)
      next := (289883)
      square := (2801303190523057353167324383280000000000000)
      linear := (-246133108928228999947897260103358000000000000)
      constant := (5484852290678945223898920985421504628937530350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227526606832175690423/50000000000000000000)
  centralHi := (455053213664351380847/100000000000000000000)
  directionLo := (457786290572060237603/100000000000000000000)
  directionHi := (114446572643015059401/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree085.table
  base := (1310669260429208185932415936056943194287/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-109716463376225052340591816105387038000000000000)
      constant := (2472765932764500085504897801003454853771368504912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree085.table
  base := (20970707710155604758500013954276935704543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-109836088404815570459620612134673038000000000000)
      constant := (2478080914563638731239848463407601846852088451573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457786290572060237603/100000000000000000000)
  centralHi := (114446572643015059401/25000000000000000000)
  directionLo := (460503147009007643871/100000000000000000000)
  directionHi := (14390723344031488871/3125000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree086.table
  base := (11125023510684094712980954107027583549503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-111006443390414098315907044816487598000000000000)
      constant := (2532626117800194712294774572415121441230617396266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree086.table
  base := (4450009326383049916583350638206610936303/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-10102497797480195631110775687615018000000000000)
      constant := (230733350407872652671409867454913181338351869515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460503147009007643871/100000000000000000000)
  centralHi := (14390723344031488871/3125000000000000000)
  directionLo := (463204068391753920499/100000000000000000000)
  directionHi := (926408136783507841/200000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree087.table
  base := (11778944651899749513130989580677131639327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-12477380378289238254580252614176462000000000000)
      constant := (288134413092106036351332569759042830194497216666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree087.table
  base := (11778944485866949673006889463576512686237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-12490984793305414824979605888095262000000000000)
      constant := (288753075527472747499457173025704552523950618446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463204068391753920499/100000000000000000000)
  centralHi := (926408136783507841/200000000000000000)
  directionLo := (465889331863421810557/100000000000000000000)
  directionHi := (232944665931710905279/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree088.table
  base := (4978846982251915170551437813985698383371/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-10326036674435653660594318385335338000000000000)
      constant := (241319702970052397209269518340794749841655232855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree088.table
  base := (3111779328519178173506745308242010584679/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-10337295500655937718855852129268138000000000000)
      constant := (241837580924357344056392690200673794616731851832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465889331863421810557/100000000000000000000)
  centralHi := (232944665931710905279/50000000000000000000)
  directionLo := (117139801656401815113/25000000000000000000)
  directionHi := (468559206625607260453/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree089.table
  base := (6564770939274981551887551917840398789061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-114876383432981236241852730949789278000000000000)
      constant := (2716547162173321043417500812530508267415161211484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree089.table
  base := (26259083515758604370540746032943875611693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-115001637874681896390012293851041678000000000000)
      constant := (2722373985599047272083291751495525329353828510223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117139801656401815113/25000000000000000000)
  centralHi := (468559206625607260453/100000000000000000000)
  directionLo := (471213954253364038209/100000000000000000000)
  directionHi := (47121395425336403821/10000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree090.table
  base := (5530487153672117913889558191531627500427/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-12907373716352253579685328851209982000000000000)
      constant := (308811222912157784898258013127133092737027926165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree090.table
  base := (3456554445330371199832087003872068654251/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-12921447249127608652512246031125982000000000000)
      constant := (309473273990520088270770344709832865973404042632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471213954253364038209/100000000000000000000)
  centralHi := (47121395425336403821/10000000000000000000)
  directionLo := (94770765798861073521/20000000000000000000)
  directionHi := (236926914497152683803/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree091.table
  base := (1860754616551090785790017473830585603/640000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-2397068233905292412091493640244702000000000000)
      constant := (58015882952475411977932610681128146044775265625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree091.table
  base := (14537145354137783350272471700639287869867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-2399681889992144068473635402229102000000000000)
      constant := (58140200632833242419280608272756547018362353426) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94770765798861073521/20000000000000000000)
  centralHi := (236926914497152683803/50000000000000000000)
  directionLo := (476479078052790615899/100000000000000000000)
  directionHi := (4764790780527906159/1000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree092.table
  base := (1220985962045227936769384734178629750369/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-118746323475548374167798417083090958000000000000)
      constant := (2906978937468374059783006520731947985594336171475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree092.table
  base := (30524648901705025462277315606447866223597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-118875799977081640837806055138318158000000000000)
      constant := (2913205080792264924423038491467853910257291525967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476479078052790615899/100000000000000000000)
  centralHi := (4764790780527906159/1000000000000000000)
  directionLo := (119772485465024027179/25000000000000000000)
  directionHi := (479089941860096108717/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree093.table
  base := (6400702045476044368556958424592346799761/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-13337367054415268904790405088243502000000000000)
      constant := (330211447169378756826295147777033112239753478095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree093.table
  base := (32003510100047481237456699027807957225889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-13351909704949802480044886174156702000000000000)
      constant := (330918357243321137397835269439952120509056255731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119772485465024027179/25000000000000000000)
  centralHi := (479089941860096108717/100000000000000000000)
  directionLo := (96337330866281157813/20000000000000000000)
  directionHi := (240843327165702894533/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree094.table
  base := (33510874375709514155034771850891430590561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-11029662136720587828948079500481098000000000000)
      constant := (276140956888656165639586874377659368641447901761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree094.table
  base := (33510874267213382391024715783308564161847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-121458574712014803803001895996502478000000000000)
      constant := (3044050234138504395208804388851013165954432246717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96337330866281157813/20000000000000000000)
  centralHi := (240843327165702894533/50000000000000000000)
  directionLo := (242134721555199588607/50000000000000000000)
  directionHi := (96853888622079835443/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree095.table
  base := (35046741465272867628992083254825441640471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (708246)
      previous := (354123)
      next := (354123)
      square := (3422090601165286129492493221680000000000000)
      linear := (-339657239662369839594859011679758000000000000)
      constant := (8598120335642060246274543399812893217397924821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree095.table
  base := (2190421335802210317150038840351507554487/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (708246)
      previous := (354123)
      next := (354123)
      square := (3422090601165286129492493221680000000000000)
      linear := (-340027595788037078353462095361758000000000000)
      constant := (8616510076412542212452250551559182610349062992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242134721555199588607/50000000000000000000)
  centralHi := (96853888622079835443/20000000000000000000)
  directionLo := (486838529802160464581/100000000000000000000)
  directionHi := (243419264901080232291/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree096.table
  base := (36611111470113903996724358575386689789583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-13767360392478284229895481325277022000000000000)
      constant := (352335085628183499655850651983515078712567270557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree096.table
  base := (36611111391365381437030042015548002987793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-13782372160771996307577526317187422000000000000)
      constant := (353088325053824471623941603322177746873361774147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486838529802160464581/100000000000000000000)
  centralHi := (243419264901080232291/50000000000000000000)
  directionLo := (122348532548770793521/25000000000000000000)
  directionHi := (97878826039016634817/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree097.table
  base := (4775498046049372723018032604536040574079/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-125196223546493604044374560638593758000000000000)
      constant := (3238833514197578748064614760238216554198187677352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree097.table
  base := (9550996075328578758334107707568082326831/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-11393885164946777113708696116707178000000000000)
      constant := (295068599799940903260878707395754101098055288124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122348532548770793521/25000000000000000000)
  centralHi := (97878826039016634817/20000000000000000000)
  directionLo := (491936454472399268509/100000000000000000000)
  directionHi := (49193645447239926851/10000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree098.table
  base := (39825360141748050711813803190828188811047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-2581351093075156122850812027544782000000000000)
      constant := (67497442280946921850879223838946874639918008733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree098.table
  base := (39825360084611561023808495416989632943351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-2584165799630227137416195463527982000000000000)
      constant := (67641615397919823887474103948394968491762421389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell115.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491936454472399268509/100000000000000000000)
  centralHi := (49193645447239926851/10000000000000000000)
  directionLo := (247232853706959775479/50000000000000000000)
  directionHi := (494465707413919550959/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree099.table
  base := (41475238774727785085527845135951361827851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12478532394148164573199899525520000000000000)
      linear := (-1290668520958299959545505232937322000000000000)
      constant := (34107467104374391318523058718754356639372856339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree099.table
  base := (8295047745213123481964369931789118210749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12478532394148164573199899525520000000000000)
      linear := (-1292075874235835466828196950928922000000000000)
      constant := (34180288843979606293521791478968356560149695305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 99 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247232853706959775479/50000000000000000000)
  centralHi := (494465707413919550959/100000000000000000000)
  directionLo := (496982088588533373209/100000000000000000000)
  directionHi := (49698208858853337321/10000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree100.table
  base := (43153620254350860303870693061806059092753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-129066163589060741970320246771895438000000000000)
      constant := (3446627228874838916728147517160867750549879073883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree100.table
  base := (43153620212909734893647644723007469160519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-129206898916814292698589418571055438000000000000)
      constant := (3453982920944721621782519535098917433076061638509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 100 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496982088588533373209/100000000000000000000)
  centralHi := (49698208858853337321/10000000000000000000)
  directionLo := (499485792537979774129/100000000000000000000)
  directionHi := (49948579253797977413/10000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree101.table
  base := (8972100913941557533219512734590477335611/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-130356143603249787945635475482995998000000000000)
      constant := (3517338628372616882659056107421365595026863374605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree101.table
  base := (22430252267209598790778484383083226512147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-130498286284280874181187339000147598000000000000)
      constant := (3524842130651511926212844728076996548367126920034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 101 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499485792537979774129/100000000000000000000)
  centralHi := (49948579253797977413/10000000000000000000)
  directionLo := (62747126119046120263/12500000000000000000)
  directionHi := (100395401790473792421/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree102.table
  base := (46595891711635869230015116421966068899451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-14627347068604314880105633799344062000000000000)
      constant := (398752604645594757877829137982753269720386276129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree102.table
  base := (2329794584079446533763818809856615361933/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-14643297072416383962642806603248862000000000000)
      constant := (399602913850953572256341521824970631210191224140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 102 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62747126119046120263/12500000000000000000)
  centralHi := (100395401790473792421/20000000000000000000)
  directionLo := (252227961418951153743/50000000000000000000)
  directionHi := (504455922837902307487/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree103.table
  base := (9671956334488728185252167260621429555207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-132936103631627879896265932905197118000000000000)
      constant := (3660931669174577354967993521165392370364018028385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree103.table
  base := (12089945411715479591032479512500884754367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-133081061019214037146383179858331918000000000000)
      constant := (3668735202952698364850376800877609511566319153748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 103 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252227961418951153743/50000000000000000000)
  centralHi := (504455922837902307487/100000000000000000000)
  directionLo := (253461357338605259309/50000000000000000000)
  directionHi := (506922714677210518619/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree104.table
  base := (50152174445678692564968781736525102884547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-134226083645816925871581161616297678000000000000)
      constant := (3733813310453990953160644619963212813947550436417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree104.table
  base := (50152174423900418955108476615656310713771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-134372448386680618628981100287424078000000000000)
      constant := (3741769065522761846874797851403105575541373626681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 104 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253461357338605259309/50000000000000000000)
  centralHi := (506922714677210518619/100000000000000000000)
  directionLo := (509377560582703252503/100000000000000000000)
  directionHi := (63672195072837906563/12500000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree105.table
  base := (12993267506483008303884442568768870007513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (254663926411187032106120398480000000000000)
      linear := (-27935696487323432662728590048938000000000000)
      constant := (784872885103921115452864669330817248290848772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree105.table
  base := (25986535003696614952426135491132106217413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (579766)
      previous := (289883)
      next := (289883)
      square := (2801303190523057353167324383280000000000000)
      linear := (-307627745474256689595417280536318000000000000)
      constant := (8651990504216488798329200051498511187578694046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 105 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509377560582703252503/100000000000000000000)
  centralHi := (63672195072837906563/12500000000000000000)
  directionLo := (511820632443298889703/100000000000000000000)
  directionHi := (63977579055412361213/12500000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree106.table
  base := (53822468408673247890830286531748610959887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-136806043674195017822211619038498798000000000000)
      constant := (3881746834722034776111559118588736754747674673157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree106.table
  base := (10764493678578664139063778652182345049253/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-136955223121613781594176941145608398000000000000)
      constant := (3890011443455039815654983351639267451280236976915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 106 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511820632443298889703/100000000000000000000)
  centralHi := (63977579055412361213/12500000000000000000)
  directionLo := (25712604903244021461/5000000000000000000)
  directionHi := (514252098064880429221/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree107.table
  base := (445602956720892789012770589567316045191/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-138096023688384063797526847749599358000000000000)
      constant := (3956798717696092906288670224281189508351872037625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree107.table
  base := (27850184788340524116919174743146100184211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-138246610489080363076774861574700558000000000000)
      constant := (3965219958802952733750258525386399006499384659042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 107 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25712604903244021461/5000000000000000000)
  centralHi := (514252098064880429221/100000000000000000000)
  directionLo := (5166721213048022929/1000000000000000000)
  directionHi := (516672121304802292901/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree108.table
  base := (57606773567078986906079282656320003878433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-15487333744730345530315786273411102000000000000)
      constant := (448063779395083079180172443034992886034661614707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree108.table
  base := (2880338677782446219903182347026259250113/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12478532394148164573199899525520000000000000)
      linear := (-1409474725823706510700735171755482000000000000)
      constant := (40819730892906751989563427722098645997504977140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 108 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5166721213048022929/1000000000000000000)
  centralHi := (516672121304802292901/100000000000000000000)
  directionLo := (519080862200753143047/100000000000000000000)
  directionHi := (64885107775094142881/12500000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree109.table
  base := (59541680336931337635549484157715332915549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-140675983716762155748157305171800478000000000000)
      constant := (4109072725296368861721238962351710942870371479839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree109.table
  base := (7442710040900567621082444505711122485497/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-140829385224013526041970702432884878000000000000)
      constant := (4117811642234947101514355542218986456151597494936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 109 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519080862200753143047/100000000000000000000)
  centralHi := (64885107775094142881/12500000000000000000)
  directionLo := (521478477094261495119/100000000000000000000)
  directionHi := (6518480963678268689/1250000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree110.table
  base := (6150508989746550661834057453145257256531/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-12905996702813745611224775807536458000000000000)
      constant := (380572259083099834839631169774280711004969917310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree110.table
  base := (3075254494459439620115296183393455576303/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-12920070235589100684051692987452458000000000000)
      constant := (381381346391882513455942171808205910424060278060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 110 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521478477094261495119/100000000000000000000)
  centralHi := (6518480963678268689/1250000000000000000)
  directionLo := (130966279687278460863/25000000000000000000)
  directionHi := (523865118749113843453/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree111.table
  base := (15874250561712317440184460489813886734459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-15917327082793360855420862510444622000000000000)
      constant := (473804487600636340686476163179230152067617191044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree111.table
  base := (6349700223980698759445059724262345770787/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-15934684439882965445240727032341022000000000000)
      constant := (474811429180211911518434500873008041777339636730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 111 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130966279687278460863/25000000000000000000)
  centralHi := (523865118749113843453/100000000000000000000)
  directionLo := (131560234116234778733/25000000000000000000)
  directionHi := (526240936464939114933/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree112.table
  base := (16379354345890584145667181928440173696309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-2949916811414883544369448802144942000000000000)
      constant := (88630802872828431859925886122411357470929549404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree112.table
  base := (65517417377570821339551189370517561840307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-2953133618906393275301315586125742000000000000)
      constant := (88819097942162029224871271557944031142610731873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 112 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131560234116234778733/25000000000000000000)
  centralHi := (526240936464939114933/100000000000000000000)
  directionLo := (66075759523274804349/12500000000000000000)
  directionHi := (528606076186198434793/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree113.table
  base := (13513267061269330873478696285482263644911/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-145835903773518339649418220016202718000000000000)
      constant := (4422301707000493352354057186691423930999341186105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree113.table
  base := (33783167650624747933972792382015247408163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-145994934693879851972362384149253518000000000000)
      constant := (4431693619940648946480701522762045650857793070786) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 113 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66075759523274804349/12500000000000000000)
  centralHi := (528606076186198434793/100000000000000000000)
  directionLo := (530960680606805348869/100000000000000000000)
  directionHi := (53096068060680534887/10000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree114.table
  base := (69643756014164542033980348376814739944151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (78694)
      previous := (39347)
      next := (39347)
      square := (380232289018365125499165913520000000000000)
      linear := (-45283436068854227646886256918222000000000000)
      constant := (1385785622375995826810690116827321144829897389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree114.table
  base := (69643756009828552090145156355768127450679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (78694)
      previous := (39347)
      next := (39347)
      square := (380232289018365125499165913520000000000000)
      linear := (-45332816885609859481366668075822000000000000)
      constant := (1388727708508543925864997134204407020695915981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 114 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530960680606805348869/100000000000000000000)
  centralHi := (53096068060680534887/10000000000000000000)
  directionLo := (133326222317647180883/25000000000000000000)
  directionHi := (533304889270588723533/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree115.table
  base := (35874839753081711303122459052452773942191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-148415863801896431600048677438403838000000000000)
      constant := (4583256681064451385818952551018855944416156486602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree115.table
  base := (8968709937809399622243537270136692419977/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-148577709428813014937558225007437838000000000000)
      constant := (4592983914175311841671004842525513798155842737176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 115 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133326222317647180883/25000000000000000000)
  centralHi := (533304889270588723533/100000000000000000000)
  directionLo := (535638838667798469719/100000000000000000000)
  directionHi := (13390970966694961743/2500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree116.table
  base := (73884105781646116759933588219944406795301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-13609622165098679779578536922682218000000000000)
      constant := (424074480808526843435046617794004757506218714501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree116.table
  base := (73884105778509104562175013372037196633689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-149869096796279596420156145436529998000000000000)
      constant := (4674716387632615431766775311858150679154079147379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 116 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535638838667798469719/100000000000000000000)
  centralHi := (13390970966694961743/2500000000000000000)
  directionLo := (537962662327842948633/100000000000000000000)
  directionHi := (268981331163921474317/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree117.table
  base := (38023517420022911531152717637783584578129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-16777313758919391505631014984511662000000000000)
      constant := (527456145620738836478197917603124973207255525382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree117.table
  base := (1188234919334028577695792617788301926899/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-16795609351527353100306007318402462000000000000)
      constant := (528574860590578059570858073890067924040581153344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 117 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537962662327842948633/100000000000000000000)
  centralHi := (268981331163921474317/50000000000000000000)
  directionLo := (540276490908436356101/100000000000000000000)
  directionHi := (270138245454218178051/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree118.table
  base := (3129538667236201919166578553889711044193/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-152285803844463569525994363571705518000000000000)
      constant := (4830114746142212969664245035757684763185306693075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree118.table
  base := (78238466678636103536789481550580612996849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-152451871531212759385351986294714318000000000000)
      constant := (4840355987222293398889511407904342009866824934139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 118 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540276490908436356101/100000000000000000000)
  centralHi := (270138245454218178051/50000000000000000000)
  directionLo := (542580452281324497649/100000000000000000000)
  directionHi := (10851609045626489953/2000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree119.table
  base := (8045840130385786455918023288518952513277/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-3134199670584747255128767189445022000000000000)
      constant := (100282603991017240542133424382071491438720067030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree119.table
  base := (80458401301928414193629882100615638162487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (474354)
      previous := (237177)
      next := (237177)
      square := (2291975337700683288955083586320000000000000)
      linear := (-285237957140406940385806877038602000000000000)
      constant := (9135924143512551836525604530692728208389920263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 119 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542580452281324497649/100000000000000000000)
  centralHi := (10851609045626489953/2000000000000000000)
  directionLo := (272437335807374054189/50000000000000000000)
  directionHi := (544874671614748108379/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree120.table
  base := (82706838708614976320686154677268030960119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-17207307096982406830736091221545182000000000000)
      constant := (555367095426559817758189300953957376196188994901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree120.table
  base := (82706838706974331723459448879349944823087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-17226071807349546927838647461433182000000000000)
      constant := (556543902634180840933002133376995672913731445373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 120 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272437335807374054189/50000000000000000000)
  centralHi := (544874671614748108379/100000000000000000000)
  directionLo := (547159271452794196087/100000000000000000000)
  directionHi := (68394908931599274511/12500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree121.table
  base := (84983778894951145131142018639228574864361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-14195976717002791586540004518637018000000000000)
      constant := (462134866907218113631492627512051831346981135561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree121.table
  base := (16996755778711233679976074681789057070643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-14211457603055682166649613416544618000000000000)
      constant := (463113819844090778843421240942800006373517181215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 121 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547159271452794196087/100000000000000000000)
  centralHi := (68394908931599274511/12500000000000000000)
  directionLo := (274717185895888875771/50000000000000000000)
  directionHi := (549434371791777751543/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree122.table
  base := (681947045802301650004789020477199895737/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-157445723901219753427255278416107758000000000000)
      constant := (5169386626980626669299191813020570972446526400896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree122.table
  base := (10911152732688574124853058497973756899271/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-157617421001079085315743668011082958000000000000)
      constant := (5180333797085088906670912516916765742346634137448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 122 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274717185895888875771/50000000000000000000)
  centralHi := (549434371791777751543/100000000000000000000)
  directionLo := (137925022538447134633/25000000000000000000)
  directionHi := (551700090153788538533/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree123.table
  base := (1792463352234363834869204620864158005317/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-17637300435045422155841167458578702000000000000)
      constant := (584001459093610877109866782315113601025828827150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree123.table
  base := (22405791902677473920923888528200102873971/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-17656534263171740755371287604463902000000000000)
      constant := (585237828900853938552466707744367627268457612836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 123 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137925022538447134633/25000000000000000000)
  centralHi := (551700090153788538533/100000000000000000000)
  directionLo := (553956541657530513213/100000000000000000000)
  directionHi := (276978270828765256607/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree124.table
  base := (22996404035482948527913491515433840076841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-160025683929597845377885735838308878000000000000)
      constant := (5343363050564855152778997738810555254059219217804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree124.table
  base := (22996404035268660701680862662509574674077/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-160200195736012248280939508869267278000000000000)
      constant := (5354672007352638575837751942023669451098260228988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 124 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553956541657530513213/100000000000000000000)
  centralHi := (276978270828765256607/50000000000000000000)
  directionLo := (556203839086574695093/100000000000000000000)
  directionHi := (278101919543287347547/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree125.table
  base := (94376567453276120713254148737296251312133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-161315663943786891353200964549409438000000000000)
      constant := (5431436383147594603074502978398588430556571743063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree125.table
  base := (94376567452547502555668253045208745267497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-161491583103478829763537429298359438000000000000)
      constant := (5442928438819851395589322778402421552008638688867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 125 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556203839086574695093/100000000000000000000)
  centralHi := (278101919543287347547/50000000000000000000)
  directionLo := (139610523238784997727/25000000000000000000)
  directionHi := (558442092955139990909/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree126.table
  base := (96796021545717378017692025822030666327487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (579766)
      previous := (289883)
      next := (289883)
      square := (2801303190523057353167324383280000000000000)
      linear := (-368720281083845662876453952971678000000000000)
      constant := (12517535441248655476809197103528761775986450877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree126.table
  base := (9679602154509805683262710045930344709287/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (579766)
      previous := (289883)
      next := (289883)
      square := (2801303190523057353167324383280000000000000)
      linear := (-369122382020284379242937300969278000000000000)
      constant := (12544013048773856321358880526083501988405786770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 126 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139610523238784997727/25000000000000000000)
  centralHi := (558442092955139990909/100000000000000000000)
  directionLo := (560671411571510530123/100000000000000000000)
  directionHi := (140167852892877632531/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree127.table
  base := (12405497302405353930118716060470519828531/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-14899602179287725754893765633782778000000000000)
      constant := (509977571808547294402767641407989158817775709848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree127.table
  base := (99243978418716443790214575322206383240131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-164074357838411992728733270156543758000000000000)
      constant := (5621615954420879032051960878336497478600333048641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 127 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560671411571510530123/100000000000000000000)
  centralHi := (140167852892877632531/25000000000000000000)
  directionLo := (28144595054959624063/5000000000000000000)
  directionHi := (562891901099192481261/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree128.table
  base := (20344087614771414552519399512862596791171/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-165185603986354029279146650682711118000000000000)
      constant := (5699996864057692163722159482323016728946316790405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree128.table
  base := (2543010951835242498063790607891197084257/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-165365745205878574211331190585635918000000000000)
      constant := (5712047038554688900973312514562900509484751409080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 128 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28144595054959624063/5000000000000000000)
  centralHi := (562891901099192481261/100000000000000000000)
  directionLo := (282551832807954029119/50000000000000000000)
  directionHi := (565103665615908058239/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree129.table
  base := (104225400509578887680972967459615526845653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-18497287111171452806051319932645742000000000000)
      constant := (643440428009078415429952930782915282598100315087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree129.table
  base := (104225400509198691232725514652331353072283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-18517459174816128410436567890525342000000000000)
      constant := (644800334101192976139717075220539890349451753857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 129 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282551832807954029119/50000000000000000000)
  centralHi := (565103665615908058239/100000000000000000000)
  directionLo := (113461361434103894701/20000000000000000000)
  directionHi := (283653403585259736753/50000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree130.table
  base := (53379432863219314388066358969679487782949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-167765564014732121229777108104912238000000000000)
      constant := (5882654253966114117644765575956096860959731802478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree130.table
  base := (5337943286305777018998065818240877000463/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-15268047267346521561502457403983658000000000000)
      constant := (535916714499007176223506232701742157187014201260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113461361434103894701/20000000000000000000)
  centralHi := (283653403585259736753/50000000000000000000)
  directionLo := (71187678229746366211/12500000000000000000)
  directionHi := (569501425837970929689/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree131.table
  base := (21864166744895202807911715116186926340533/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-169055544028921167205092336816012798000000000000)
      constant := (5975068069710986854631308835660514680318655677315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree131.table
  base := (27330208431050367839666653038651831385693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-169239907308278318659124951872912398000000000000)
      constant := (5987689596289787552489127660076092717171083296892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71187678229746366211/12500000000000000000)
  centralHi := (569501425837970929689/100000000000000000000)
  directionLo := (571687619772332345151/100000000000000000000)
  directionHi := (8932619058942692893/1562500000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree132.table
  base := (111911304503738283680813658165090723467121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12478532394148164573199899525520000000000000)
      linear := (-1720661859021315284650581469970842000000000000)
      constant := (61295003023398047246503387810216493807409903369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree132.table
  base := (55955652251752502803748034279352990289057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12478532394148164573199899525520000000000000)
      linear := (-1722538330058029294360837093959642000000000000)
      constant := (61424446639524723218446857124207894090446258546) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571687619772332345151/100000000000000000000)
  centralHi := (8932619058942692893/1562500000000000000)
  directionLo := (143466371314506090917/25000000000000000000)
  directionHi := (573865485258024363669/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree133.table
  base := (28632569516069664625384859634449173507253/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (14454)
      previous := (7227)
      next := (7227)
      square := (69838583697250737336581494320000000000000)
      linear := (-9702951215857270572430481894862000000000000)
      constant := (348355811113260601889061485324942872708872188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree133.table
  base := (114530278064080453851728660298874788520517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (14454)
      previous := (7227)
      next := (7227)
      square := (69838583697250737336581494320000000000000)
      linear := (-9713532819447763108390570000062000000000000)
      constant := (349091283993366170298458288426824604063531183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143466371314506090917/25000000000000000000)
  centralHi := (573865485258024363669/100000000000000000000)
  directionLo := (576035116759300288387/100000000000000000000)
  directionHi := (144008779189825072097/25000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree134.table
  base := (117177754406155052046000119843138548411873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-172925484071488305131038022949314478000000000000)
      constant := (6256650000109268601702392957217117442502904528203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree134.table
  base := (117177754405986656751685117592718297380127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-173114069410678063106918713160188878000000000000)
      constant := (6269856112027010358250298012417750914273349583797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576035116759300288387/100000000000000000000)
  centralHi := (144008779189825072097/25000000000000000000)
  directionLo := (144549151742014222571/25000000000000000000)
  directionHi := (115639321393611378057/20000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree135.table
  base := (4794149341177159850225826313738783527421/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-19357273787297483456261472406712782000000000000)
      constant := (705773052366324430830767437956065363999551268975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree135.table
  base := (119853733529285934820766227575546178326883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-19378384086460516065501848176586782000000000000)
      constant := (707262376190902805613048889604838419832666567257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144549151742014222571/25000000000000000000)
  centralHi := (115639321393611378057/20000000000000000000)
  directionLo := (58035004685004255749/10000000000000000000)
  directionHi := (580350046850042557491/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree136.table
  base := (61279107717082373346402508514664028356229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-175505444099866397081668480371515598000000000000)
      constant := (6447988356345533139186712235309766943523480286638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree136.table
  base := (30639553858510803576413264754906499698433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-175696844145611226072114554018373198000000000000)
      constant := (6461591543632112562768231247185236472973570209452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58035004685004255749/10000000000000000000)
  centralHi := (580350046850042557491/100000000000000000000)
  directionLo := (72811940711190995163/12500000000000000000)
  directionHi := (116499105137905592261/20000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree137.table
  base := (125291200120428538740991158180804855011877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-176795424114055443056983709082616158000000000000)
      constant := (6544742655255224378964005953893317211950204133047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree137.table
  base := (15661400015040662621361552244264382276351/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-176988231513077807554712474447465358000000000000)
      constant := (6558546585769089285992409511375949581204407288488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72811940711190995163/12500000000000000000)
  centralHi := (116499105137905592261/20000000000000000000)
  directionLo := (292316565566250652589/50000000000000000000)
  directionHi := (584633131132501305179/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree138.table
  base := (128052687588287970692646096943218771913541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12478532394148164573199899525520000000000000)
      linear := (-1798842465941863525578777149431482000000000000)
      constant := (67093135030566787633152462343590842856378626749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree138.table
  base := (64026343794100139077198581445819485140513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-19808846542282709893034488319617502000000000000)
      constant := (739580723569908294275582723764937635198311758054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292316565566250652589/50000000000000000000)
  centralHi := (584633131132501305179/100000000000000000000)
  directionLo := (586762949228447283483/100000000000000000000)
  directionHi := (146690737307111820871/25000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree139.table
  base := (65421338918905746715594025355246296778749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-179375384142433535007614166504817278000000000000)
      constant := (6740421494658315801280977389576924552256419630078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree139.table
  base := (8177667364858563074314323702816184808559/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-179571006248010970519908315305649678000000000000)
      constant := (6754631322712489244457740649926445993036502639184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586762949228447283483/100000000000000000000)
  centralHi := (146690737307111820871/25000000000000000000)
  directionLo := (588885064470766096761/100000000000000000000)
  directionHi := (294442532235383048381/50000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree140.table
  base := (133661170869067989613972201480742918227341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-3687048248094338387406722351345262000000000000)
      constant := (139578490513305234363835233310198251154526939999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree140.table
  base := (133661170869004727427722267433458473871531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-3691069257458725551071555831321262000000000000)
      constant := (139872673826921516655798417817707652397694646409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588885064470766096761/100000000000000000000)
  centralHi := (294442532235383048381/50000000000000000000)
  directionLo := (4617184061217861249/781250000000000000)
  directionHi := (590999559835886239873/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree141.table
  base := (136508166682126427959839210008426018172331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-20217260463423514106471624880779822000000000000)
      constant := (770999332167461644678003396916037203189953993649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree141.table
  base := (136508166682072699757680643270662571800679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12478532394148164573199899525520000000000000)
      linear := (-1839937181645900338233375314786202000000000000)
      constant := (70238541379285769337820179447350202232582210831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4617184061217861249/781250000000000000)
  centralHi := (590999559835886239873/100000000000000000000)
  directionLo := (593106516821122289791/100000000000000000000)
  directionHi := (4633644662665017889/781250000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree142.table
  base := (13938366527705558051820532746932581078729/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-183245324185000672933559852638118958000000000000)
      constant := (7039365357724031190472720092348581848434620908190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree142.table
  base := (4355739539906560991272319558962442596431/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-183445168350410714967702076592926158000000000000)
      constant := (7054195059803020667676065016876219833975632894112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593106516821122289791/100000000000000000000)
  centralHi := (4633644662665017889/781250000000000000)
  directionLo := (595206015481326562343/100000000000000000000)
  directionHi := (74400751935165820293/12500000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree143.table
  base := (142287666653923792712663186805039069471729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-16775936745380883537170461940838138000000000000)
      constant := (649132739982064121472508188258067453898968728529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree143.table
  base := (142287666653885044237199325194929565389513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-16794232337988845131845454274728938000000000000)
      constant := (650499946116405717315241576899317425739575859113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595206015481326562343/100000000000000000000)
  centralHi := (74400751935165820293/12500000000000000000)
  directionLo := (149324533616095318511/25000000000000000000)
  directionHi := (119459626892876254809/20000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree144.table
  base := (5808806832511951902675641835503383282433/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-20647253801486529431576701117813342000000000000)
      constant := (804697592860366206010307681484570128392813267675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree144.table
  base := (72610085406382946757826514101624943365297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-20669771453927097548099768605678942000000000000)
      constant := (806392070997970752047823129865910047710152249926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149324533616095318511/25000000000000000000)
  centralHi := (119459626892876254809/20000000000000000000)
  directionLo := (119876590209115145791/20000000000000000000)
  directionHi := (149845737761393932239/25000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree145.table
  base := (148181177753747566881587177346340930198603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-187115264227567810859505538771420638000000000000)
      constant := (7344819945545920025912329902625316031714025758233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree145.table
  base := (18522647219214953383122971096458633633617/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-187319330452810459415495837880202638000000000000)
      constant := (7360282754906959855996320532946562822113280481496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119876590209115145791/20000000000000000000)
  centralHi := (149845737761393932239/25000000000000000000)
  directionLo := (37591283822556940269/6250000000000000000)
  directionHi := (120292108232182208861/20000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree146.table
  base := (75585343738418096639006306831478453618087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-188405244241756856834820767482521198000000000000)
      constant := (7448084969210693593781643532584517286477967506714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree146.table
  base := (75585343738406234925662870234789647129153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-188610717820277040898093758309294798000000000000)
      constant := (7463761755056248127054563265607457713477382308566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37591283822556940269/6250000000000000000)
  centralHi := (120292108232182208861/20000000000000000000)
  directionLo := (603530979439373026009/100000000000000000000)
  directionHi := (60353097943937302601/10000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree147.table
  base := (3854717499553244949753556588132069264667/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (579766)
      previous := (289883)
      next := (289883)
      square := (2801303190523057353167324383280000000000000)
      linear := (-430147900807133566462893415405038000000000000)
      constant := (17124883008475579588938731195140348881999706280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree147.table
  base := (154188699982109655589019862570148280357653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (579766)
      previous := (289883)
      next := (289883)
      square := (2801303190523057353167324383280000000000000)
      linear := (-430617018566312068890457321402238000000000000)
      constant := (17160919817300942901594696241172694821300240063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603530979439373026009/100000000000000000000)
  centralHi := (60353097943937302601/10000000000000000000)
  directionLo := (605594339234212000221/100000000000000000000)
  directionHi := (302797169617106000111/50000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree148.table
  base := (15723521526969246010172122874128325009621/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-190985204270134948785451224904722318000000000000)
      constant := (7656785258127143256729665019524673465684234010310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree148.table
  base := (157235215269675358953617683082612363719081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-191193492555210203863289599167479118000000000000)
      constant := (7672894408027475317040161165136467704080855557091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605594339234212000221/100000000000000000000)
  centralHi := (302797169617106000111/50000000000000000000)
  directionLo := (37978168290829168371/6250000000000000000)
  directionHi := (607650692653266693937/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree149.table
  base := (160310233339587163610584351953827674973687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-17479562207665817705524223055983898000000000000)
      constant := (705656411216276533279502688418847086683485944087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree149.table
  base := (5009694791861645161788470055052537899549/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-192484879922676785345887519596571278000000000000)
      constant := (7778548060849637059893455440954070450323427322848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37978168290829168371/6250000000000000000)
  centralHi := (607650692653266693937/100000000000000000000)
  directionLo := (609700110588367631307/100000000000000000000)
  directionHi := (152425027647091907827/25000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree150.table
  base := (163413754191875759280559229111615800253601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-21507240477612560081786853591880382000000000000)
      constant := (874264355832614971166060822714860640797545428979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree150.table
  base := (10213359636991464628307266178203259819079/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-21530696365571485203165048891740382000000000000)
      constant := (876102955321812164753984646826733593477385163856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609700110588367631307/100000000000000000000)
  centralHi := (152425027647091907827/25000000000000000000)
  directionLo := (122348532548770793521/20000000000000000000)
  directionHi := (305871331371926983803/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree151.table
  base := (166545777826618938728113097215069097597817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-194855144312702086711396911038023998000000000000)
      constant := (7975261295470728163816083721578701992473370706387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree151.table
  base := (41636444456652118962936417462084270098363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-195067654657609948311083360454755598000000000000)
      constant := (7992030019167598972260335162314121054892897470372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122348532548770793521/20000000000000000000)
  centralHi := (305871331371926983803/50000000000000000000)
  directionLo := (24551136706569448609/4000000000000000000)
  directionHi := (306889208832118107613/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree152.table
  base := (10606644015242263662558454001959871664091/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (708246)
      previous := (354123)
      next := (354123)
      square := (3422090601165286129492493221680000000000000)
      linear := (-543338294534324467276210913432478000000000000)
      constant := (22390212748783175518690457519076013399080087056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree152.table
  base := (42426576060966834264460048681028132781547/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (311099145560480557226590292880000000000000)
      linear := (-49448260394126549935452349756698000000000000)
      constant := (2039752788885321037975094269443029626226648908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24551136706569448609/4000000000000000000)
  centralHi := (306889208832118107613/50000000000000000000)
  directionLo := (38487965172564745083/6250000000000000000)
  directionHi := (615807442761035921329/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree153.table
  base := (2701489585057905203920879334113377199767/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-21937233815675575406891929828913902000000000000)
      constant := (910132858112625721244062572802247757617821637952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree153.table
  base := (43223833360924598541191151618895862892159/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-21961158821393679030697689034771102000000000000)
      constant := (912045723820493813439980714006434348422773624244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38487965172564745083/6250000000000000000)
  centralHi := (615807442761035921329/100000000000000000000)
  directionLo := (154457451084708007657/25000000000000000000)
  directionHi := (617829804338832030629/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree154.table
  base := (176112865426165232994866473652812424930653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (474354)
      previous := (237177)
      next := (237177)
      square := (2291975337700683288955083586320000000000000)
      linear := (-368692178766733255356850829631402000000000000)
      constant := (15399347045602121769903675264204105568599691597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree154.table
  base := (11007054089134927128831936223772541971979/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (474354)
      previous := (237177)
      next := (237177)
      square := (2291975337700683288955083586320000000000000)
      linear := (-369094279703171971723334177629002000000000000)
      constant := (15431706100798149454640491402877639821871356336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154457451084708007657/25000000000000000000)
  centralHi := (617829804338832030629/100000000000000000000)
  directionLo := (154961391905135601419/25000000000000000000)
  directionHi := (619845567620542405677/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree155.table
  base := (44839725047827522725121766474557754804287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-200015064369458270612657825882426238000000000000)
      constant := (8410023806008560810193049182624660956394280966228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree155.table
  base := (179358900191304659774235007953676563511079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-200233204127476274241475042171124238000000000000)
      constant := (8427692546500982620189782529734674828462800166669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154961391905135601419/25000000000000000000)
  centralHi := (619845567620542405677/100000000000000000000)
  directionLo := (310927398385983888549/50000000000000000000)
  directionHi := (621854796771967777099/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree156.table
  base := (22829179717399413755274708072297738149761/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-22367227153738590731997006065947422000000000000)
      constant := (946724774255642110215381379678606904731538764952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree156.table
  base := (5707294929349709391783165043173057879237/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-22391621277215872858230329177801822000000000000)
      constant := (948713376544097836770263249690281405730689799136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310927398385983888549/50000000000000000000)
  centralHi := (621854796771967777099/100000000000000000000)
  directionLo := (623857554925624254399/100000000000000000000)
  directionHi := (389910971828515159/62500000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree157.table
  base := (185936478069874537343331311797225430788027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-202595024397836362563288283304627358000000000000)
      constant := (8631745544456292126296487650850334964875731550697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree157.table
  base := (46484119517467656330904739444137580287967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-202815978862409437206670883029308558000000000000)
      constant := (8649873115517990273976313352041913620454683912148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623857554925624254399/100000000000000000000)
  centralHi := (389910971828515159/62500000000000000)
  directionLo := (125170780840777888169/20000000000000000000)
  directionHi := (312926952101944720423/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree158.table
  base := (47317005295850069767027796371693612657013/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-203885004412025408538603512015727918000000000000)
      constant := (8743691534475192162814691419502777586458801570972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree158.table
  base := (2957312830990577486367975639506428336647/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-204107366229876018689268803458400718000000000000)
      constant := (8762050726364403831668256351805777583926267489088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125170780840777888169/20000000000000000000)
  centralHi := (312926952101944720423/50000000000000000000)
  directionLo := (9810061027210721261/1562500000000000000)
  directionHi := (125568781148297232141/20000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree159.table
  base := (192628067079823918748854731559999800865723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-22797220491801606057102082302980942000000000000)
      constant := (984040104261952120544450765537721064252651515617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree159.table
  base := (7705122683192844055556087349360120562923/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-22822083733038066685762969320832542000000000000)
      constant := (986105913492912357252555715036458440475324860425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9810061027210721261/1562500000000000000)
  centralHi := (125568781148297232141/20000000000000000000)
  directionLo := (314913809853663410497/50000000000000000000)
  directionHi := (125965523941465364199/20000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree160.table
  base := (9800830787959786841853179504942141879827/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-18769542221854863680839451767084458000000000000)
      constant := (815432159645773722202939881862727958588206764540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree160.table
  base := (39203323151838669213928049099328078528659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-206690140964809181654464644316585038000000000000)
      constant := (8988580600733500500129977147287576798641257280245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314913809853663410497/50000000000000000000)
  centralHi := (125965523941465364199/20000000000000000000)
  directionLo := (31590255266287024507/5000000000000000000)
  directionHi := (631805105325740490141/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree161.table
  base := (99716833610782465826815135753605428345153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-4239896825603929519684677513245502000000000000)
      constant := (185385101790063344845964598887576905807254846134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree161.table
  base := (39886733444312580592910476610287240311301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 357390000000000000000000000000000000000000000
      center := (5217894)
      previous := (2608947)
      next := (2608947)
      square := (25211728714707516178505919449520000000000000)
      linear := (-4244520986372974757899236015217902000000000000)
      constant := (185774140086864446183124970410593970407427932195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31590255266287024507/5000000000000000000)
  centralHi := (631805105325740490141/100000000000000000000)
  directionLo := (126755284179420776047/20000000000000000000)
  directionHi := (158444105224275970059/25000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree162.table
  base := (25359902683372455160765067756371124354801/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-23227213829864621382207158540014462000000000000)
      constant := (1022078848131825804945366773105720450046662590232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree162.table
  base := (202879221466977919905047290104910010480897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1945790000000000000000000000000000000000000000
      center := (28408534)
      previous := (14204267)
      next := (14204267)
      square := (137263856335629810305198894780720000000000000)
      linear := (-23252546188860260513295609463863262000000000000)
      constant := (1024223334667207513423825521526355228929362457363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126755284179420776047/20000000000000000000)
  centralHi := (158444105224275970059/25000000000000000000)
  directionLo := (317870811908948282759/50000000000000000000)
  directionHi := (635741623817896565519/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree163.table
  base := (103176639247743483071070842294075519822151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-210334904482970638415179655571230718000000000000)
      constant := (9314272692523578468152351895291754749286537749722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree163.table
  base := (206353278495485505572984135119570273734847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112306791547333481158799095729680000000000000)
      linear := (-19142209369746266009296218691260138000000000000)
      constant := (848528367634464751899614804945841111148861377247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317870811908948282759/50000000000000000000)
  centralHi := (635741623817896565519/100000000000000000000)
  directionLo := (318850385300099977549/50000000000000000000)
  directionHi := (637700770600199955099/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree164.table
  base := (209855838307132991919025250977828263649341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-211624884497159684390494884282331278000000000000)
      constant := (9430559165724623274164527841774756543413626101951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree164.table
  base := (209855838307131752691668548512145087083073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-211855690434675507584856326032953678000000000000)
      constant := (9450338960179172531301195808467978862095835351403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318850385300099977549/50000000000000000000)
  centralHi := (637700770600199955099/100000000000000000000)
  directionLo := (79956739611332345099/12500000000000000000)
  directionHi := (639653916890658760793/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree165.table
  base := (213386900901962812792992891727488353739177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12478532394148164573199899525520000000000000)
      linear := (-2150655197084330609755657707004362000000000000)
      constant := (96440091442319652848103677678862196489292301953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree165.table
  base := (213386900901961761403057203540122296712081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12478532394148164573199899525520000000000000)
      linear := (-2153000785880223121893477236990362000000000000)
      constant := (96642330915203306887832572158184803306540000809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79956739611332345099/12500000000000000000)
  centralHi := (639653916890658760793/100000000000000000000)
  directionLo := (64160111748892295927/10000000000000000000)
  directionHi := (641601117488922959271/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree166.table
  base := (13559154142501284666684079849988065404199/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-214204844525537776341125341704532398000000000000)
      constant := (9665302353718722815312105227136537118072843759824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree166.table
  base := (43389293256003932535061006471511546310973/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-214438465169608670550052166891137998000000000000)
      constant := (9685567445257054105315322926873638480633926691515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64160111748892295927/10000000000000000000)
  centralHi := (641601117488922959271/100000000000000000000)
  directionLo := (128708485273117507937/20000000000000000000)
  directionHi := (321771213182793769843/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree167.table
  base := (220534534441349398346120978332136428978767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-215494824539726822316440570415632958000000000000)
      constant := (9783759068511930442915173893510603118928335536837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree167.table
  base := (8821381377653945664565914606988080606093/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-215729852537075252032650087320230158000000000000)
      constant := (9804269014135028327793091407066330926656918215575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128708485273117507937/20000000000000000000)
  centralHi := (321771213182793769843/50000000000000000000)
  directionLo := (161369474169911662977/25000000000000000000)
  directionHi := (645477896679646651909/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree168.table
  base := (224151105385991602536044738138294243678151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (579766)
      previous := (289883)
      next := (289883)
      square := (2801303190523057353167324383280000000000000)
      linear := (-491575520530421470049332877838398000000000000)
      constant := (22455644438025719997010047125099750441645937621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree168.table
  base := (224151105385990960576149584795871497697909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (579766)
      previous := (289883)
      next := (289883)
      square := (2801303190523057353167324383280000000000000)
      linear := (-492111655112339758537977341835198000000000000)
      constant := (22502710810066040951547461854893429717358396639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell115.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161369474169911662977/25000000000000000000)
  centralHi := (645477896679646651909/100000000000000000000)
  directionLo := (323703790397739062361/50000000000000000000)
  directionHi := (647407580795478124723/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree169.table
  base := (227796179113988526578206788767062279624289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-218074784568104914267071027837834078000000000000)
      constant := (10022842739691031471544646343342709998763130763979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree169.table
  base := (113898089556993991001161986612913943609031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17512110000000000000000000000000000000000000000
      center := (255676806)
      previous := (127838403)
      next := (127838403)
      square := (1235374707020668292746790053026480000000000000)
      linear := (-218312627272008414997845928178414478000000000000)
      constant := (10043846804569413735195030925896993972203029573082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell115.Kernel169
