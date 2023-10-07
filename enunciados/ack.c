#include <stdio.h>

unsigned ack(unsigned m, unsigned n) {
    if (m == 0)
        return n+1;

    if(n == 0)
        return ack(m-1,1);
    return ack(m-1,ack(m,n-1));
}

int main() {
    printf("%d\n",ack(3,11));
    return 0;
}