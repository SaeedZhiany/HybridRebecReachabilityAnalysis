public class HelloJNI {  // Save as HelloJNI.java
//   static {
//      System.loadLibrary("hypro"); // Load native library hello.dll (Windows) or libhello.so (Unixes)
//                                   //  at runtime
//                                   // This library contains a native method called sayHello()
//   }

    // Declare an instance native method sayHello() which receives no parameter and returns void
    public native double[] sayHello(String[] ODEs, double[] intervals, double[] reachParams);
    public native double[] doTimeStep(String[] ODEs, double[] intervals, double[] reachParams);
    public native double[] intersectWithGuard(int xDim, int yDim, double[] guardMat, double[] guardVec);

//   // Test Driver
//   public static void main(String[] args) {
////      String[] ODEs = {"x'=-0.5-y-1.5*x*x-0.5*x*x*x", "y'=3*x-y"};
//      String[] ODEs = {"timer'=1", "tempr'=0.1"};
//      double [] intervals = new double [] {0.8, 1.2, 0.8, 1.2};
//
//      // reachability parameters
//      // Max_iter_number(int), Stop_ration, timeStepSize, Taylor_model_Order(int), Time
//      double [] reachParams = new double [] {50.0, 0.99, 0.01, 7.0, 5};
//
//      double[] resultArray = new HelloJNI().sayHello(ODEs, intervals, reachParams);  // Create an instance and invoke the native method
//
//      System.out.println("Results from Java");
//
//      for (int i = 0; i<resultArray.length; i++)
//         System.out.println(resultArray[i]);
//
//   }
}
