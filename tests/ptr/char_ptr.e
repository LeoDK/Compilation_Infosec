void f(char* p, char c){
    *p = c;
}

int main()
{
    char a = 'k';
    int b = 42;
    char c = 'o';
    char* pa = &a;
    int* pb = &b;
    char* pc = &c;
    f(pa, 'O');
    f(pc, 'K');
    print_char(a);
    print_char(c);
    return 0;
}
