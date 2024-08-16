class Test3Node {
	Test3Node f;
	Test3Node g;
	Test3Node() {}
}

public class Test3 {
    public static void main(String[] args) {
        Test3Node a = new Test3Node(); //O1
        a.f = new Test3Node(); //O2
        a.f.f = new Test3Node(); // O3
        a.f.f.f = new Test3Node(); //O4
        a.f.f.f.f = new Test3Node(); //O5
        a.f.f.f.f.f = new Test3Node(); //O6
        Test3Node b = foo(a);
        a = new Test3Node(); //O7
        // Lots of other code
    }

    static Test3Node foo(Test3Node x) {
        while(x != null) {
            x = x.f;
        }
        return x;
    }
}