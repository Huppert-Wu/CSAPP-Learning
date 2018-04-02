#include <stdio.h>
static int position(size_t size)
{
    int x = 0;
    x += (!!(size>>(16+x)))<<4;
    x += (!!(size>>(8+x)))<<3;
    x += (!!(size>>(4+x)))<<2;
    x += (!!(size>>(2+x)))<<1;
    x += (!!(size>>(1+x)));
    return (!!(size&(~(1<<x)))+x);


}
int main()
{
    int result1 = position(8);
    int x = position(0);
    int y = position(1);
    int z = position(7);
    int a = position(9);
    printf("8 = %d\n", result1);
    printf("0 = %d\n", x);
    printf("1 = %d\n", y);
    printf("7 = %d\n", z);
    printf("9 = %d\n", a);
}
