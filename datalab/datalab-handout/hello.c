#include<stdio.h>
unsigned float_i2f(int x) {
    unsigned y,result,mask,sign,add=0,count=0;
    mask=0x80000000;
    sign=mask&x;
    y=x;


    if(x<0)
        y=-x;
    while(!(mask&y))
    {
        count+=1;
        mask>>=1;
    }

    y<<=count+1;
    if(((y&0x1ff)>0x100)||((y&0x3ff)>=0x300))
        add=1;

    if(!x)
        result = x;
    result = sign + ((158-count)<<23) + (y>>9)+add ;
    printf("%x",result);
    return result;
}

int main()
{
    float_i2f(0x80800000);
}
