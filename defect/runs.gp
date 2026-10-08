\\ The recorded runs of defect.gp: gp -q defect.gp runs.gp < /dev/null > logs/gp_runs.log
forprime(l = 5, 199, scan(l, 211));
{
  foreach([[7,58],[11,14],[11,15],[11,16],[13,21],[13,22],[13,23],[17,16],[17,17],[17,18],[17,19],[19,15],[19,16],
           [19,17],[19,18],[23,14],[23,15],[23,16],[23,17]], v, run(v[1], v[2], 0));
}
